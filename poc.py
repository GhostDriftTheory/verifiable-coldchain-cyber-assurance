#!/usr/bin/env python3
"""Public reference model, Lean correspondence and minimal evidence verifier.
It does NOT contain or re-evaluate the private gate.

Checks signatures, the declared trial roster, complete observations, public result
consistency and arithmetic. Use an independently received key-set fingerprint to
pin the signer; bundled keys alone do not authenticate an organization.
Signature verification only: cryptography. Public model execution needs only Python 3.10+. No network, dynamic imports or code in the input.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

SCHEMA = 'cca.public-evidence.v2'
SCOPE = 'synthetic-only;separate-process-same-administrator;not-third-party-attestation'
DOMAIN = b'CCA-SHOWCASE-v2\x00'
LIMIT = 600_000
GROUPS = {'prevention', 'containment', 'normal', 'recovery', 'negative_control'}
OUTCOMES = {'STOPPED', 'QUARANTINED', 'RELEASED', 'LIMIT_OBSERVED'}
CHECK_NAMES = ('baseline_tests', 'disclosure_tests', 'finite_observations',
               'finite_guards', 'bounded_states', 'bounded_transitions', 'input_comparisons')

class Rejected(ValueError):
    pass

def exact(x, names):
    if type(x) is not dict or set(x) != set(names):
        raise Rejected('Unexpected fields or object type')
    return x

def integer(x, low=0, high=100_000):
    if type(x) is not int or not low <= x <= high:
        raise Rejected('Invalid integer')
    return x

def hexstr(x, n=64):
    if type(x) is not str or not re.fullmatch(r'[0-9a-f]{' + str(n) + r'}', x):
        raise Rejected('Invalid hexadecimal value')
    return x

def _tree(x, depth=0):
    if depth > 15:
        raise Rejected('Nesting limit')
    if x is None or type(x) is bool:
        return
    if type(x) is int:
        integer(x, -2**53 + 1, 2**53 - 1)
    elif type(x) is str:
        if len(x) > 5000:
            raise Rejected('String limit')
        x.encode('utf-8', 'strict')
    elif type(x) is list:
        if len(x) > 512:
            raise Rejected('Array limit')
        for v in x:
            _tree(v, depth + 1)
    elif type(x) is dict:
        if len(x) > 64 or any(type(k) is not str for k in x):
            raise Rejected('Object limit')
        for k, v in x.items():
            _tree(k, depth + 1); _tree(v, depth + 1)
    else:
        raise Rejected('Unsupported JSON value')

def canon(x):
    _tree(x)
    return json.dumps(x, ensure_ascii=False, sort_keys=True,
                      separators=(',', ':'), allow_nan=False).encode('utf-8')

def sha(x):
    return hashlib.sha256(canon(x)).hexdigest()

def _pairs(items):
    result = {}
    for k, v in items:
        if k in result:
            raise Rejected('Duplicate JSON key')
        result[k] = v
    return result

def _bad_number(_):
    raise Rejected('Only bounded JSON integers are allowed')

def load_bytes(raw):
    if type(raw) is not bytes or len(raw) > LIMIT:
        raise Rejected('Input byte limit')
    try:
        x = json.loads(raw.decode('utf-8', 'strict'), object_pairs_hook=_pairs,
                       parse_float=_bad_number, parse_constant=_bad_number)
        _tree(x)
        return x
    except (UnicodeError, RecursionError, json.JSONDecodeError) as e:
        raise Rejected('Invalid JSON') from e

def load_file(path):
    with Path(path).open('rb') as f:
        return load_bytes(f.read(LIMIT + 1))

def signed(env, public_key, kind):
    try:
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
        from cryptography.exceptions import InvalidSignature
    except ImportError as exc:
        raise Rejected('Signature verification needs cryptography. Run: python -m pip install cryptography . Or use the browser verifier.') from exc
    exact(env, ('kind', 'payload', 'signature'))
    if env['kind'] != kind:
        raise Rejected('Signature domain mismatch')
    hexstr(env['signature'], 128)
    try:
        Ed25519PublicKey.from_public_bytes(bytes.fromhex(hexstr(public_key))).verify(
            bytes.fromhex(env['signature']), DOMAIN + kind.encode('ascii') + b'\x00' + canon(env['payload']))
    except (InvalidSignature, ValueError) as e:
        raise Rejected('Signature verification failed') from e
    return env['payload']

def summarize(plan, obs, rows):
    totals = {'cases': 0, 'expectations_met': 0, 'prevention_cases': 0,
              'target_calls_prevented': 0, 'containment_cases': 0, 'quarantined_cases': 0,
              'normal_recovery_cases': 0, 'normal_recovery_released': 0,
              'negative_controls': 0, 'limits_observed': 0,
              'all_wms_calls': 0, 'all_wms_effects': 0}
    for p, o, r in zip(plan, obs, rows):
        totals['cases'] += 1
        totals['expectations_met'] += int(r['expected_matched'])
        totals['all_wms_calls'] += o['calls_total']
        totals['all_wms_effects'] += o['effects_total']
        g = p['category']
        if g == 'prevention':
            totals['prevention_cases'] += 1
            totals['target_calls_prevented'] += int(r['outcome'] == 'STOPPED' and o['calls_target'] == 0 and o['effects_target'] == 0)
        elif g == 'containment':
            totals['containment_cases'] += 1
            totals['quarantined_cases'] += int(r['outcome'] == 'QUARANTINED' and o['calls_target'] > 0)
        elif g in ('normal', 'recovery'):
            totals['normal_recovery_cases'] += 1
            totals['normal_recovery_released'] += int(r['outcome'] == 'RELEASED' and o['calls_target'] > 0)
        else:
            totals['negative_controls'] += 1
            totals['limits_observed'] += int(r['outcome'] == 'LIMIT_OBSERVED' and o['calls_target'] > 0)
    return totals

def verify(bundle, expected_keyset=None, expected_challenge=None):
    _tree(bundle)
    exact(bundle, ('schema', 'keys', 'plan', 'observation', 'report'))
    if bundle['schema'] != SCHEMA:
        raise Rejected('Schema mismatch')
    keys = exact(bundle['keys'], ('observer', 'publisher'))
    for k in keys.values(): hexstr(k)
    if keys['observer'] == keys['publisher']:
        raise Rejected('Role keys must be distinct')
    fingerprint = sha(keys)
    if expected_keyset is not None and fingerprint != hexstr(expected_keyset):
        raise Rejected('Pinned key-set mismatch')
    plan = signed(bundle['plan'], keys['observer'], 'plan')
    exact(plan, ('schema', 'run_id', 'challenge', 'build_commitment', 'scope', 'cases'))
    if plan['schema'] != 'cca.public-plan.v2' or plan['scope'] != SCOPE:
        raise Rejected('Plan scope mismatch')
    hexstr(plan['run_id'], 32); hexstr(plan['challenge']); hexstr(plan['build_commitment'])
    if expected_challenge is not None and plan['challenge'] != hexstr(expected_challenge):
        raise Rejected('Challenge mismatch')
    if type(plan['cases']) is not list or len(plan['cases']) != 50:
        raise Rejected('The published suite must contain exactly 50 trials')
    ids = []
    for row in plan['cases']:
        exact(row, ('case_id', 'category', 'title'))
        if type(row['case_id']) is not str or not re.fullmatch(r'P[0-9]{2}', row['case_id']):
            raise Rejected('Invalid public trial ID')
        if row['category'] not in GROUPS:
            raise Rejected('Invalid group')
        if type(row['title']) is not str or not 1 <= len(row['title']) <= 60:
            raise Rejected('Invalid public title')
        ids.append(row['case_id'])
    if ids != [f'P{i:02d}' for i in range(1, 51)]:
        raise Rejected('Trial roster order, uniqueness or completeness mismatch')
    obs = signed(bundle['observation'], keys['observer'], 'observation')
    exact(obs, ('schema', 'run_id', 'challenge', 'plan_sha256', 'closed', 'scope', 'cases'))
    if obs['schema'] != 'cca.public-observation.v2' or obs['scope'] != SCOPE or obs['closed'] is not True:
        raise Rejected('Observation is not a closed, declared observation')
    if (obs['run_id'], obs['challenge'], obs['plan_sha256']) != (plan['run_id'], plan['challenge'], sha(bundle['plan'])):
        raise Rejected('Observation does not match the plan')
    if type(obs['cases']) is not list or len(obs['cases']) != 50:
        raise Rejected('Observation count mismatch')
    for cid, row in zip(ids, obs['cases']):
        exact(row, ('case_id', 'calls_total', 'effects_total', 'calls_target', 'effects_target'))
        if row['case_id'] != cid: raise Rejected('Observation roster mismatch')
        for field in ('calls_total', 'effects_total', 'calls_target', 'effects_target'):
            integer(row[field], 0, 20)
        if row['calls_target'] > row['calls_total'] or row['effects_target'] > row['effects_total']:
            raise Rejected('Target window exceeds complete case observation')
        if row['effects_total'] > 2 * row['calls_total'] or row['effects_target'] > 2 * row['calls_target']:
            raise Rejected('Impossible simulator count')
    report = signed(bundle['report'], keys['publisher'], 'report')
    exact(report, ('schema', 'run_id', 'challenge', 'plan_sha256', 'observation_sha256',
                   'build_commitment', 'cases', 'metrics', 'checks', 'assurance'))
    if report['schema'] != 'cca.public-report.v2': raise Rejected('Report schema mismatch')
    if (report['run_id'], report['challenge'], report['plan_sha256'], report['observation_sha256'], report['build_commitment']) != (
            plan['run_id'], plan['challenge'], sha(bundle['plan']), sha(bundle['observation']), plan['build_commitment']):
        raise Rejected('Report binding mismatch')
    if report['assurance'] != 'publisher-reported-outcomes;not-reexecution-of-private-policy':
        raise Rejected('Assurance scope mismatch')
    if type(report['cases']) is not list or len(report['cases']) != 50: raise Rejected('Report count mismatch')
    for p, o, r in zip(plan['cases'], obs['cases'], report['cases']):
        exact(r, ('case_id', 'outcome', 'expected_matched'))
        if r['case_id'] != p['case_id'] or r['outcome'] not in OUTCOMES or type(r['expected_matched']) is not bool:
            raise Rejected('Invalid result row')
        # These checks concern public observations, not hidden authorization rules.
        if r['outcome'] == 'STOPPED' and (o['calls_target'] or o['effects_target']):
            raise Rejected('A stopped target cannot have a simulator call or effect')
        if r['outcome'] in ('RELEASED', 'LIMIT_OBSERVED') and (o['calls_target'] != 1 or o['effects_target'] != 1):
            raise Rejected('A released target needs one observed call and effect')
        if r['outcome'] == 'QUARANTINED' and o['calls_target'] < 1:
            raise Rejected('Post-execution quarantine needs an observed call')
    metrics = summarize(plan['cases'], obs['cases'], report['cases'])
    exact(report['metrics'], metrics)
    for name, value in report['metrics'].items(): integer(value)
    if report['metrics'] != metrics: raise Rejected('Public metric mismatch')
    if (metrics['prevention_cases'], metrics['containment_cases'], metrics['normal_recovery_cases'], metrics['negative_controls']) != (37, 7, 5, 1):
        raise Rejected('Declared suite population mismatch')
    checks = exact(report['checks'], (*CHECK_NAMES, 'lean', 'external_audit'))
    for name in CHECK_NAMES:
        exact(checks[name], ('status', 'count'))
        if checks[name]['status'] not in ('PASS', 'NOT_RUN'): raise Rejected('Invalid check status')
        integer(checks[name]['count'])
        if (checks[name]['status'] == 'PASS') != (checks[name]['count'] > 0): raise Rejected('Check status/count mismatch')
    if checks['lean'] != 'NOT_RUN' or checks['external_audit'] != 'NOT_PERFORMED':
        raise Rejected('Unsupported assurance claim')
    return {'status': 'PASS', 'keyset_sha256': fingerprint,
            'signer_pin_matched': expected_keyset is not None,
            'challenge_matched': expected_challenge is not None,
            'organization_authenticated': False, 'private_policy_reexecuted': False,
            'metrics': metrics, 'run_id': plan['run_id'],
            'scope': 'public-record-integrity-and-observation-consistency-only'}

# PUBLIC REFERENCE MODEL — only coarse, synthetic conditions are exposed.
# This is not a transcription, compilation or approximation claim of the private gate.
import copy
import itertools
import secrets
import tempfile
import unittest

MODEL = 'cca.coarse-public-model.v1'
DEMO_SCOPE = 'public-reference-only;synthetic;not-private-engine;not-sensor-authentication'
INPUT_FIELDS = ('quality','records_complete','authorized','evidence_intact','upstream_clear','change_before_execution','result_matches')
CASES = [{'id': 'normal', 'title': '正常な引き渡し', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'RELEASED', 'description': '確認が揃った要求は、模擬引き渡しまで進みます。'}, {'id': 'missing', 'title': '記録が不足', 'input': {'quality': 'ok', 'records_complete': False, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'HOLD', 'description': '温度の申告が正常でも、必要な記録がなければ保留します。'}, {'id': 'unauthorized', 'title': '受領権限が不一致', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': False, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': '品質とは別に、受領を認められた要求かを確認します。'}, {'id': 'tampered', 'title': '証拠が不整合', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': False, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': '根拠が一致しない要求を、正常な引き渡しに使いません。'}, {'id': 'quality_fail', 'title': '品質条件が不成立', 'input': {'quality': 'fail', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': 'この例の条件に反する荷物は、次の区間へ進めません。'}, {'id': 'changed', 'title': '許可後に状況が変化', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': True, 'result_matches': True}, 'expected': 'DENIED', 'description': '最初の確認だけでなく、実行直前にも成立を確認します。'}, {'id': 'result_mismatch', 'title': '実行結果が不一致', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': False}, 'expected': 'QUARANTINED', 'description': '実行は発生しますが、成功確定と下流への継続を止めます。'}, {'id': 'upstream', 'title': '上流の保留が未解消', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': False, 'change_before_execution': False, 'result_matches': True}, 'expected': 'HOLD', 'description': '現在の荷物だけでなく、前の区間の未解決事項も確認します。'}, {'id': 'quality_review', 'title': '品質担当者の確認が必要', 'input': {'quality': 'review', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'HOLD', 'description': '自動的に進めず、人の確認が必要な状態として保留します。'}, {'id': 'missing_and_auth', 'title': '不足と権限不一致', 'input': {'quality': 'ok', 'records_complete': False, 'authorized': False, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': '不足の補完だけでは、権限不一致は解消しません。'}, {'id': 'missing_and_integrity', 'title': '不足と証拠不整合', 'input': {'quality': 'ok', 'records_complete': False, 'authorized': True, 'evidence_intact': False, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': '資料の追加だけで不整合を無視することはありません。'}, {'id': 'review_and_auth', 'title': '要確認と権限不一致', 'input': {'quality': 'review', 'records_complete': True, 'authorized': False, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': '品質確認を優先して権限の不成立を通すことはありません。'}, {'id': 'fail_and_missing', 'title': '品質不成立と記録不足', 'input': {'quality': 'fail', 'records_complete': False, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': '条件違反がある場合は、単なる保留と区別します。'}, {'id': 'fail_and_upstream', 'title': '品質不成立と上流保留', 'input': {'quality': 'fail', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': False, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': '複数の問題がある場合も、実行には進みません。'}, {'id': 'auth_and_integrity', 'title': '権限と証拠の不一致', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': False, 'evidence_intact': False, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'DENIED', 'description': '一つの成立を理由に別の不成立を上書きしません。'}, {'id': 'missing_and_upstream', 'title': '記録不足と上流保留', 'input': {'quality': 'ok', 'records_complete': False, 'authorized': True, 'evidence_intact': True, 'upstream_clear': False, 'change_before_execution': False, 'result_matches': True}, 'expected': 'HOLD', 'description': '未解決の条件が残る間は引き渡しを保留します。'}, {'id': 'review_and_missing', 'title': '要確認と記録不足', 'input': {'quality': 'review', 'records_complete': False, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': True}, 'expected': 'HOLD', 'description': '確認事項を揃える前に実行しません。'}, {'id': 'review_and_upstream', 'title': '要確認と上流保留', 'input': {'quality': 'review', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': False, 'change_before_execution': False, 'result_matches': True}, 'expected': 'HOLD', 'description': '品質確認だけで上流の保留は解消されません。'}, {'id': 'missing_and_change', 'title': '記録不足のまま状況変化', 'input': {'quality': 'ok', 'records_complete': False, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': True, 'result_matches': True}, 'expected': 'HOLD', 'description': '実行前の不足を確認した時点で保留します。'}, {'id': 'upstream_and_change', 'title': '上流保留のまま状況変化', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': False, 'change_before_execution': True, 'result_matches': True}, 'expected': 'HOLD', 'description': '前の区間が未解決なら実行段階へ進みません。'}, {'id': 'review_and_change', 'title': '要確認のまま状況変化', 'input': {'quality': 'review', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': True, 'result_matches': True}, 'expected': 'HOLD', 'description': '人の確認を必要とする状態は自動実行しません。'}, {'id': 'auth_and_change', 'title': '権限不一致と状況変化', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': False, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': True, 'result_matches': True}, 'expected': 'DENIED', 'description': '権限不一致は実行前に拒否します。'}, {'id': 'integrity_and_change', 'title': '証拠不整合と状況変化', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': False, 'upstream_clear': True, 'change_before_execution': True, 'result_matches': True}, 'expected': 'DENIED', 'description': '不整合な根拠を使う要求は実行しません。'}, {'id': 'change_and_result', 'title': '状況変化と結果異常の設定', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': True, 'result_matches': False}, 'expected': 'DENIED', 'description': '直前の不成立で止まるため、結果確認には進みません。'}, {'id': 'missing_and_result', 'title': '記録不足と結果異常の設定', 'input': {'quality': 'ok', 'records_complete': False, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': False}, 'expected': 'HOLD', 'description': '実行しない場合、結果異常の設定は作用しません。'}, {'id': 'auth_and_result', 'title': '権限不一致と結果異常の設定', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': False, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': False}, 'expected': 'DENIED', 'description': '拒否した操作は模擬WMSへ渡しません。'}, {'id': 'integrity_and_result', 'title': '証拠不整合と結果異常の設定', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': False, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': False}, 'expected': 'DENIED', 'description': '根拠が不整合な要求は実行しません。'}, {'id': 'review_and_result', 'title': '要確認と結果異常の設定', 'input': {'quality': 'review', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': True, 'change_before_execution': False, 'result_matches': False}, 'expected': 'HOLD', 'description': '確認を要する要求は保留し、実行しません。'}, {'id': 'upstream_and_result', 'title': '上流保留と結果異常の設定', 'input': {'quality': 'ok', 'records_complete': True, 'authorized': True, 'evidence_intact': True, 'upstream_clear': False, 'change_before_execution': False, 'result_matches': False}, 'expected': 'HOLD', 'description': '上流の保留がある間は結果確認へ進みません。'}, {'id': 'multiple_failures', 'title': '複数条件が同時に不成立', 'input': {'quality': 'fail', 'records_complete': False, 'authorized': False, 'evidence_intact': False, 'upstream_clear': False, 'change_before_execution': True, 'result_matches': False}, 'expected': 'DENIED', 'description': '複数の問題が重なっても、自動実行には進みません。'}]
BUILTIN_KEYSET = '7f62d163c1ca4defd66919a0f539ef87ccefe13d7f7711426dcdf24e838fee27'
CASE_BY_ID = {x['id']: x for x in CASES}


def validate_input(value):
    exact(value, INPUT_FIELDS)
    if type(value['quality']) is not str or value['quality'] not in ('ok','review','fail'):
        raise Rejected('quality must be ok, review or fail')
    for field in INPUT_FIELDS[1:]:
        if type(value[field]) is not bool:
            raise Rejected(field + ' must be a JSON boolean')
    return value


class _MockHandoff:
    """Local synthetic effect sink; never a real shipment or an external service."""
    def __init__(self):
        self.calls = 0
        self.events = []

    def release(self):
        self.calls += 1
        self.events.append('synthetic-handoff')


def transition(value, state):
    """Small public example: precheck, one immediate recheck, simulated action, postcheck."""
    validate_input(value)
    exact(state, ('consumed', 'quarantined'))
    if any(type(state[k]) is not bool for k in state):
        raise Rejected('State flags must be booleans')
    operation = _MockHandoff()
    reasons = []
    status = 'RELEASED'
    stage = 'complete'
    if state['quarantined']:
        status, stage, reasons = 'DENIED', 'precheck', ['QUARANTINE_LOCK']
    elif state['consumed']:
        status, stage, reasons = 'DENIED', 'precheck', ['ALREADY_EXECUTED']
    else:
        for condition, code in ((not value['authorized'],'AUTHORITY_MISMATCH'),
                                (not value['evidence_intact'],'EVIDENCE_MISMATCH'),
                                (value['quality']=='fail','QUALITY_FAILED')):
            if condition: reasons.append(code)
        if reasons:
            status, stage = 'DENIED', 'precheck'
        else:
            for condition, code in ((not value['records_complete'],'RECORDS_MISSING'),
                                    (not value['upstream_clear'],'UPSTREAM_UNRESOLVED'),
                                    (value['quality']=='review','QUALITY_REVIEW')):
                if condition: reasons.append(code)
            if reasons:
                status, stage = 'HOLD', 'precheck'
            elif value['change_before_execution']:
                status, stage, reasons = 'DENIED', 'recheck', ['CONDITIONS_CHANGED']
    result = {'status':status,'stage':stage,'reasons':reasons,
              'calls':0,'effects':0,'confirmed':0,'quarantined':False}
    next_state = dict(state)
    if status == 'RELEASED':
        # Only this branch invokes the local mock operation. It does not control a real WMS.
        operation.release()
        result['calls'] = operation.calls
        result['effects'] = len(operation.events)
        next_state['consumed'] = True
        if value['result_matches']:
            result['confirmed'] = 1
        else:
            result.update(status='QUARANTINED', stage='postcheck', reasons=['RESULT_MISMATCH'], quarantined=True)
            next_state['quarantined'] = True
    return result, next_state


def summarize_steps(steps):
    return {path: {key:sum(step[path][key] for step in steps) for key in ('calls','effects','confirmed')}
            for path in ('without_checks','with_checks')}


def make_session(inputs, session_id=None):
    if type(inputs) is not list or not 1 <= len(inputs) <= 32:
        raise Rejected('A session must contain 1–32 public-model attempts')
    session_id = secrets.token_hex(16) if session_id is None else hexstr(session_id,32)
    state = {'consumed':False,'quarantined':False}
    steps = []
    for seq, value in enumerate(inputs,1):
        validate_input(value)
        result, state = transition(value,state)
        steps.append({'sequence':seq,'input':copy.deepcopy(value),
                      'without_checks':{'calls':1,'effects':1,'confirmed':1}, 'with_checks':result})
    payload = {'schema':'cca.public-demo.session.v3','model':MODEL,'scope':DEMO_SCOPE,
               'session_id':session_id,'steps':steps,'totals':summarize_steps(steps)}
    return {'payload':payload,'sha256':sha(payload)}


def verify_session(record):
    _tree(record)
    exact(record,('payload','sha256'))
    payload = exact(record['payload'],('schema','model','scope','session_id','steps','totals'))
    if payload['schema']!='cca.public-demo.session.v3' or payload['model']!=MODEL or payload['scope']!=DEMO_SCOPE:
        raise Rejected('Public reference model or scope mismatch')
    if sha(payload) != hexstr(record['sha256']):
        raise Rejected('Public demo record hash mismatch')
    if type(payload['steps']) is not list or not 1 <= len(payload['steps']) <= 32:
        raise Rejected('Invalid attempt count')
    for s in payload['steps']:
        exact(s,('sequence','input','without_checks','with_checks'))
        integer(s['sequence'],1,32)
    recalculated = make_session([s['input'] for s in payload['steps']], payload['session_id'])
    if canon(record) != canon(recalculated):
        raise Rejected('Public model replay disagrees with saved decisions or operation counts')
    return {'status':'PASS','attempts':len(payload['steps']),'scope':'public-model-replay;not-external-attestation'}


def make_pack(sessions):
    if type(sessions) is not list or not 1 <= len(sessions) <= 100:
        raise Rejected('Pack must contain 1–100 public sessions')
    for record in sessions: verify_session(record)
    payload={'schema':'cca.public-demo.pack.v3','model':MODEL,'scope':DEMO_SCOPE,'sessions':copy.deepcopy(sessions)}
    return {'payload':payload,'sha256':sha(payload)}


def verify_artifact(record):
    if type(record) is dict and record.get('schema') == SCHEMA:
        return verify(record, expected_keyset=BUILTIN_KEYSET)
    exact(record, ('payload','sha256'))
    if type(record['payload']) is not dict: raise Rejected('Payload must be an object')
    if record['payload'].get('schema') != 'cca.public-demo.pack.v3':
        return verify_session(record)
    p=exact(record['payload'],('schema','model','scope','sessions'))
    if p['model']!=MODEL or p['scope']!=DEMO_SCOPE or sha(p)!=hexstr(record['sha256']):
        raise Rejected('Pack model, scope or digest mismatch')
    if type(p['sessions']) is not list or not 1<=len(p['sessions'])<=100:
        raise Rejected('Pack count mismatch')
    attempts=0
    for session in p['sessions']: attempts+=verify_session(session)['attempts']
    return {'status':'PASS','sessions':len(p['sessions']),'attempts':attempts,
            'scope':'public-model-replay;not-external-attestation'}


def public_tests():
    results=[]
    def check(name, test):
        test()
        results.append(name)
    def eq(a,b):
        if a!=b:raise AssertionError((a,b))
    for row in CASES:
        def t(row=row):
            r=make_session([row['input']],'0'*32)
            eq(r['payload']['steps'][0]['with_checks']['status'],row['expected'])
            verify_session(r)
        check('case:'+row['id'],t)
    for quality in ('ok','review','fail'):
        for bits in itertools.product((False,True),repeat=6):
            x=dict(zip(INPUT_FIELDS,(quality,*bits)))
            # Independently written expected-case partition, not the transition's reason logic.
            allowed = quality=='ok' and all(bits[:4]) and not bits[4]
            hard = quality=='fail' or not bits[1] or not bits[2]
            soft = quality=='review' or not bits[0] or not bits[3]
            expected='DENIED' if hard else 'HOLD' if soft else 'DENIED' if bits[4] else 'RELEASED' if bits[5] else 'QUARANTINED'
            def t(x=x,expected=expected,allowed=allowed):
                r=make_session([x],'0'*32);s=r['payload']['steps'][0]['with_checks']
                eq(s['status'],expected);eq(s['calls'],int(allowed));eq(s['effects'],int(allowed))
                eq(s['confirmed'],int(allowed and x['result_matches']));verify_session(r)
            check('combination:'+quality+':'+''.join(map(lambda b:str(int(b)),bits)),t)
    base=CASE_BY_ID['normal']['input']
    invalid=[]
    for key in INPUT_FIELDS:
        x=dict(base);del x[key];invalid.append(x)
    for key in INPUT_FIELDS[1:]:
        x=dict(base);x[key]='true';invalid.append(x)
        x=dict(base);x[key]=1;invalid.append(x)
    invalid.extend([{**base,'quality':'unknown'},{**base,'unexpected':True},[],None])
    for i,x in enumerate(invalid):
        def t(x=x):
            try:make_session([x]);raise AssertionError('Invalid input accepted')
            except Rejected:pass
        check('invalid:'+str(i),t)
    original=make_session([base],'0'*32)
    for i in range(10):
        for rehash in (False,True):
            x=copy.deepcopy(original);p=x['payload'];s=p['steps'][0]
            if i==0:s['with_checks']['status']='DENIED'
            elif i==1:s['with_checks']['effects']=0
            elif i==2:s['with_checks']['calls']=0
            elif i==3:s['with_checks']['confirmed']=0
            elif i==4:s['with_checks']['stage']='precheck'
            elif i==5:s['without_checks']['effects']=0
            elif i==6:p['scope']='production-certified'
            elif i==7:s['sequence']=2
            elif i==8:p['totals']['with_checks']['calls']=2
            else:s['with_checks']['reasons']=['AUTHORITY_MISMATCH']
            if rehash:x['sha256']=sha(p)
            def t(x=x):
                try:verify_session(x);raise AssertionError('Modified record accepted')
                except Rejected:pass
            check('mutation:'+str(i)+':rehash='+str(rehash),t)
    for i,inputs,expect in [
      ('recovery',[CASE_BY_ID['missing']['input'],base],['HOLD','RELEASED']),
      ('repeat',[base,base],['RELEASED','DENIED']),
      ('quarantine',[CASE_BY_ID['result_mismatch']['input'],base],['QUARANTINED','DENIED'])]:
        def t(inputs=inputs,expect=expect):
            r=make_session(inputs,'0'*32);verify_session(r)
            eq([s['with_checks']['status'] for s in r['payload']['steps']],expect)
        check(i,t)
    for i,text in enumerate(['{"a":1,"a":2}','{"a":NaN}','{"a":1.5}','{"a":1e3}']):
        def t(text=text):
            try:load_bytes(text.encode());raise AssertionError('Invalid JSON accepted')
            except Rejected:pass
        check('strict-json:'+str(i),t)
    return {'status':'PASS','model':MODEL,'total':len(results),'representative_cases':30,
            'input_combinations':192,'additional_checks':len(results)-222,
            'checks':results,'scope':'public-reference-only;not-private-tests'}


def main(argv=None):
    import html
    import http.server
    from datetime import datetime
    parser=argparse.ArgumentParser(description='Cold Chain Cyber Assurance — compact public reference PoC. No private engine is included.')
    sub=parser.add_subparsers(dest='cmd')
    run=sub.add_parser('run');run.add_argument('--case',choices=list(CASE_BY_ID));run.add_argument('--out');run.add_argument('--complete',action='store_true');run.add_argument('--repeat',action='store_true')
    sub.add_parser('test')
    vp=sub.add_parser('verify');vp.add_argument('file')
    ve=sub.add_parser('verify-evidence');ve.add_argument('file',nargs='?',default=str(Path(__file__).with_name('evidence.json')));ve.add_argument('--expected-keyset')
    serve=sub.add_parser('serve');serve.add_argument('--port',type=int,default=8767)
    a=parser.parse_args(argv)
    try:
        if a.cmd=='test':result=public_tests()
        elif a.cmd=='verify':result=verify_artifact(load_file(a.file))
        elif a.cmd=='verify-evidence':
            result=verify(load_file(a.file),expected_keyset=a.expected_keyset or BUILTIN_KEYSET)
            result['pin_source']='user-supplied' if a.expected_keyset else 'bundled-reference-not-identity-authority'
        elif a.cmd=='serve':
            if not 1024<=a.port<=65535:raise Rejected('port must be 1024–65535')
            root=Path(__file__).resolve().parent
            allowed={'/':'index.html','/index.html':'index.html','/evidence.json':'evidence.json','/README.md':'README.md','/poc.py':'poc.py','/ColdChainPublic.lean':'ColdChainPublic.lean','/lean-toolchain':'lean-toolchain'}
            class Handler(http.server.BaseHTTPRequestHandler):
                def do_GET(self):
                    if self.headers.get('Host') not in (f'127.0.0.1:{a.port}',f'localhost:{a.port}'):
                        self.send_error(403);return
                    name=allowed.get(self.path)
                    if name is None:self.send_error(404);return
                    data=(root/name).read_bytes()
                    self.send_response(200)
                    self.send_header('Content-Type',{'index.html':'text/html; charset=utf-8','evidence.json':'application/json; charset=utf-8'}.get(name,'text/plain; charset=utf-8'))
                    self.send_header('X-Content-Type-Options','nosniff');self.send_header('Cache-Control','no-store');self.send_header('Content-Length',str(len(data)));self.end_headers();self.wfile.write(data)
                def log_message(self,*args):pass
            with http.server.ThreadingHTTPServer(('127.0.0.1',a.port),Handler) as server:
                print(f'http://127.0.0.1:{a.port}/ — public static demo only; no private-engine connection',flush=True)
                try:server.serve_forever()
                except KeyboardInterrupt:pass
            return 0
        else:
            chosen=CASE_BY_ID.get(getattr(a,'case',None))
            complete=getattr(a,'complete',False);repeat=getattr(a,'repeat',False)
            if complete and repeat:raise Rejected('Use either --complete or --repeat')
            if (complete or repeat) and chosen is None:raise Rejected('Specify --case for a multi-step run')
            if complete and chosen['id']!='missing':raise Rejected('--complete is the synthetic missing-record example only')
            selected=[chosen] if chosen else CASES
            sessions=[]
            for row in selected:
                inputs=[row['input']]
                if complete:inputs.append({**row['input'],'records_complete':True})
                if repeat:inputs.append(dict(row['input']))
                sessions.append(make_session(inputs))
            pack=make_pack(sessions);checks=public_tests()
            dest=Path(getattr(a,'out',None) or (str(Path.home()/'coldchain-assurance-results'/'run-')+datetime.now().strftime('%Y%m%d-%H%M%S')+'-'+secrets.token_hex(3)))
            dest.mkdir(parents=True,exist_ok=False)
            (dest/'records.json').write_bytes(canon(pack)+b'\n')
            (dest/'checks.json').write_bytes(canon(checks)+b'\n')
            source=Path(__file__).with_name('index.html').read_text(encoding='utf-8')
            marker='<script type="application/json" id="saved-records">null</script>'
            if source.count(marker)!=1:raise Rejected('The matching public index.html is required')
            embedded=canon(pack).decode().replace('<','\\u003c').replace('&','\\u0026').replace('>','\\u003e')
            source=source.replace(marker,'<script type="application/json" id="saved-records">'+embedded+'</script>')
            (dest/'report.html').write_text(source,encoding='utf-8')
            verified=verify_artifact(load_file(dest/'records.json'))
            result={'status':'PASS','sessions':len(sessions),'self_tests':checks['total'],'verified':verified,'report':str((dest/'report.html').resolve()),'scope':DEMO_SCOPE}
        print(json.dumps(result,ensure_ascii=False,indent=2));return 0
    except (Rejected,OSError,ValueError,TypeError,KeyError,AssertionError) as exc:
        print('FAIL: '+str(exc),file=sys.stderr);return 2


# Public verification is confined to the existing coarse model.
# No private engine or external inference client is distributed.
import os
import shutil
import subprocess
from datetime import datetime, timezone

PUBLIC_FILES = ('index.html','poc.py','evidence.json','ColdChainPublic.lean',
                'lean-toolchain','README.md','.github/workflows/verify.yml')
STATUS_CODE = {'DENIED':0,'HOLD':1,'RELEASED':2,'QUARANTINED':3}
STAGE_CODE = {'precheck':0,'recheck':1,'complete':2,'postcheck':3}
REASON_CODE = {k:i for i,k in enumerate(('QUARANTINE_LOCK','ALREADY_EXECUTED',
 'AUTHORITY_MISMATCH','EVIDENCE_MISMATCH','QUALITY_FAILED','RECORDS_MISSING',
 'UPSTREAM_UNRESOLVED','QUALITY_REVIEW','CONDITIONS_CHANGED','RESULT_MISMATCH'))}


def matrix_rows():
    rows=[]
    for c,z in itertools.product((False,True),repeat=2):
        state={'consumed':c,'quarantined':z}
        for q in ('ok','review','fail'):
            for bs in itertools.product((False,True),repeat=6):
                x=dict(zip(INPUT_FIELDS,(q,*bs)))
                y,nxt=transition(x,state)
                fp=[STATUS_CODE[y['status']],STAGE_CODE[y['stage']],y['calls'],y['effects'],
                    y['confirmed'],int(y['quarantined']),int(nxt['consumed']),int(nxt['quarantined'])]
                fp.extend(REASON_CODE[r] for r in y['reasons'])
                rows.append({'state':state.copy(),'input':x,'result':y,'next':nxt,'fingerprint':fp})
    return rows


def lean_correspondence(rows):
    lines=['import ColdChainPublic','open ColdChainPublic','set_option maxRecDepth 4096',
           'set_option maxHeartbeats 0','-- Concrete output equality; NOT whole-language equivalence.']
    for row in rows:
        s=row['state'];x=row['input'];b=lambda v:'true' if v else 'false'
        ss='⟨'+b(s['consumed'])+', '+b(s['quarantined'])+'⟩'
        xx='⟨.'+x['quality']+', '+', '.join(b(x[k]) for k in INPUT_FIELDS[1:])+'⟩'
        lines.append(f'example : fingerprint {ss} {xx} = {row["fingerprint"]} := by decide')
    return '\n'.join(lines)+'\n'


def cross_check():
    """The exact embedded JS and Python functions, every typed input and state."""
    if not shutil.which('node'):raise Rejected('Node.js is required for Python/JavaScript correspondence')
    root=Path(__file__).resolve().parent
    script=r'''const fs=require('fs'),vm=require('vm'),crypto=require('crypto');
const h=fs.readFileSync(process.argv[1],'utf8');
const m=h.match(/<script id="cca-core">([\s\S]*?)<\/script>/);if(!m)throw Error('core missing');
const box={crypto:crypto.webcrypto,TextEncoder,TextDecoder,Uint8Array,Uint32Array,DataView,DOMException};
vm.createContext(box);vm.runInContext(m[1],box,{timeout:15000});
const rows=JSON.parse(fs.readFileSync(0,'utf8'));
const out=rows.map(r=>{box.x=r.input;box.s=r.state;return vm.runInContext('transition(x,s)',box)});
(async()=>{const cases=box.CCA.strictParse(h.match(/<script type="application\/json" id="public-cases">([\s\S]*?)<\/script>/)[1]);
const self=await box.CCA.publicTests(cases);
const e=box.CCA.strictParse(fs.readFileSync(process.argv[2],'utf8'));
const pin=crypto.createHash('sha256').update(box.CCA.canonical(e.keys)).digest('hex');
const v=await box.CCA.verifyPublic(e,pin);
let rejected=0;for(let i=0;i<50;i++){const d=JSON.parse(JSON.stringify(e));d.observation.payload.cases[i].effects_target^=1;
try{await box.CCA.verifyPublic(d,pin)}catch{rejected++;}}
if(rejected!==50)throw Error('Modified evidence accepted');
process.stdout.write(JSON.stringify({out,tests:self.total,evidence:v.metrics.cases,rejected}));
})().catch(e=>{console.error(e);process.exit(2)});'''
    rows=matrix_rows()
    p=subprocess.run(['node','-e',script,str(root/'index.html'),str(root/'evidence.json')],
        input=json.dumps(rows),text=True,capture_output=True,timeout=90,check=False)
    if p.returncode:raise Rejected('JavaScript check failed: '+p.stderr[:2000])
    result=json.loads(p.stdout)
    if len(result['out'])!=len(rows):raise Rejected('Missing JavaScript results')
    for i,(r,js) in enumerate(zip(rows,result['out'])):
        if canon(r['result'])!=canon(js['result']) or canon(r['next'])!=canon(js['state']):
            raise Rejected(f'JavaScript/Python difference at state/input {i}')
    return {'status':'PASS','typed_state_input_pairs':len(rows),'javascript_tests':result['tests'],
      'signed_evidence_cases':result['evidence'],'signed_mutations_rejected':result['rejected'],
      'scope':'public-model-only;all-typed-states;not-parser-or-runtime-proof'}


def formal_check():
    root=Path(__file__).resolve().parent
    source=(root/'ColdChainPublic.lean').read_text(encoding='utf-8')
    if re.search(r'\b(sorry|admit|native_decide)\b',re.sub(r'/-.*?-/', '',source,flags=re.S)):
        # Comments are stripped first; no trusted-native shortcut or proof holes.
        source_code=re.sub(r'--[^\n]*','',re.sub(r'/-.*?-/', '',source,flags=re.S))
        if re.search(r'\b(sorry|admit|native_decide)\b',source_code):raise Rejected('Forbidden proof shortcut')
    if re.search(r'^\s*(axiom|unsafe)\b',source,flags=re.M):raise Rejected('Unapproved axiom or unsafe code')
    required={'step_properties','trace_at_most_once','replay_cannot_repeat','hold_does_not_consume','normal_progress','evidence_completion_progress','mismatch_then_replay_stops'}
    theorem_names=set(re.findall(r'^theorem\s+(\w+)',source,re.M))
    if len(theorem_names)!=37 or not required.issubset(theorem_names):raise Rejected('Expected public proof obligations missing')
    if re.findall(r'^import\s+(.+)$',source,re.M)!=['Std']:raise Rejected('Unexpected formal dependency')
    if not shutil.which('lean'):raise Rejected('LEAN_UNAVAILABLE: install the toolchain in lean-toolchain; no proof PASS is issued')
    version=subprocess.run(['lean','--version'],cwd=root,text=True,capture_output=True,timeout=180,check=False)
    if version.returncode or not re.match(r'^Lean \(version 4\.32\.1,',version.stdout):
        raise Rejected('Pinned Lean 4.32.1 is required: '+(version.stdout+version.stderr)[:1000])
    if (root/'lean-toolchain').read_text(encoding='utf-8').strip()!='leanprover/lean4:v4.32.1':
        raise Rejected('Toolchain file mismatch')
    compared=cross_check()
    rows=matrix_rows();generated=lean_correspondence(rows)
    names=re.findall(r'^theorem\s+(\w+)',source,re.M)
    with tempfile.TemporaryDirectory(prefix='cca-public-proof-') as tmp:
        tmp=Path(tmp);(tmp/'ColdChainPublic.lean').write_text(source,encoding='utf-8')
        (tmp/'lean-toolchain').write_bytes((root/'lean-toolchain').read_bytes())
        (tmp/'Correspondence.lean').write_text(generated,encoding='utf-8')
        (tmp/'Audit.lean').write_text('import ColdChainPublic\n'+''.join('#print axioms ColdChainPublic.'+n+'\n' for n in names))
        env=dict(os.environ);env['LEAN_PATH']=str(tmp)
        logs=[]
        for args in [['lean','-o','ColdChainPublic.olean','ColdChainPublic.lean'],
                     ['lean','Correspondence.lean'],['lean','Audit.lean']]:
            p=subprocess.run(args,cwd=tmp,env=env,text=True,capture_output=True,timeout=300,check=False)
            text=p.stdout+p.stderr;logs.append(text)
            if p.returncode or 'sorryAx' in text or 'Lean.ofReduceBool' in text:
                raise Rejected('Lean verification failed:\n'+text[:6000])
        audit=logs[-1]
        if any('ColdChainPublic.'+name not in audit for name in names):raise Rejected('Missing proof-dependency audit entry')
        for group in re.findall(r'depends on axioms:\s*\[(.*?)\]',audit,re.S):
            deps={x.strip() for x in group.split(',') if x.strip()}
            if not deps.issubset({'propext','Classical.choice','Quot.sound'}):
                raise Rejected('Unapproved theorem dependency: '+str(sorted(deps)))
        if 'sorryAx' in ''.join(logs):raise Rejected('Proof hole in dependency audit')
        # A verifier that accepts every file must fail this command. These are
        # deliberately false, closed claims over the same public model.
        invalid = {
          'unauthorized_call': '(step initial { normal with authorized := false }).calls = 1',
          'missing_record_call': '(step initial { normal with records := false }).calls = 1',
          'duplicate_effect': 'totalEffects initial [normal, normal] = 2',
          'mismatch_confirmed': '(step initial { normal with resultMatches := false }).confirmed = 1',
          'altered_observation': 'fingerprint initial normal = [2, 2, 0, 1, 1, 0, 1, 0]',
        }
        negative = []
        for name, claim in invalid.items():
            file = tmp / (name + '.lean')
            file.write_text('import ColdChainPublic\nopen ColdChainPublic\nexample : ' + claim + ' := by decide\n', encoding='utf-8')
            p = subprocess.run(['lean', file.name], cwd=tmp, env=env,
                text=True, capture_output=True, timeout=60, check=False)
            message = p.stdout + p.stderr
            if p.returncode == 0 or 'decide' not in message or 'is false' not in message:
                raise Rejected('Negative proof check failed: ' + name + '\n' + message[:1500])
            negative.append(name)
    return {'status':'PASS','lean_version':version.stdout.strip(),'theorems':len(names),
       'concrete_implementation_equalities':len(rows),'false_claims_rejected':negative,'correspondence':compared,
       'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
       'python_sha256':hashlib.sha256((root/'poc.py').read_bytes()).hexdigest(),
       'javascript_sha256':hashlib.sha256(re.search(r'<script id="cca-core">(.*?)</script>',(root/'index.html').read_text(encoding='utf-8'),re.S).group(1).encode()).hexdigest(),
       'certificate_sha256':hashlib.sha256(generated.encode()).hexdigest(),
       'axiom_audit':'\n'.join(logs),'scope':'public-model;not-private-kernel-or-full-runtime-verification'}


def public_audit():
    root=Path(__file__).resolve().parent
    # A checkout has Git metadata; bytecode is runtime-only. Neither is packed.
    paths=[]
    for p in root.rglob('*'):
        rel=p.relative_to(root)
        if rel.parts[0]=='.git' or '__pycache__' in rel.parts:continue
        if p.is_symlink():raise Rejected('Symlink not allowed: '+rel.as_posix())
        if p.is_dir() and rel.as_posix() not in ('.github','.github/workflows'):
            raise Rejected('Unapproved directory: '+rel.as_posix())
        if p.is_file():paths.append(p)
    actual={p.relative_to(root).as_posix() for p in paths}
    if actual!=set(PUBLIC_FILES):raise Rejected('Public allowlist mismatch: '+str(sorted(actual^set(PUBLIC_FILES))))
    for name in PUBLIC_FILES:
        p=root/name
        if p.is_symlink() or p.stat().st_size>600000:raise Rejected('Symlink/size limit: '+name)
    evidence=load_file(root/'evidence.json')
    proof=verify(evidence,expected_keyset=BUILTIN_KEYSET)
    h=(root/'index.html').read_text(encoding='utf-8')
    embedded=re.search(r'<script type="application/json" id="public-evidence">(.*?)</script>',h,re.S)
    if not embedded or load_bytes(embedded.group(1).encode())!=evidence:raise Rejected('HTML evidence substitution')
    model_cases=re.search(r'<script type="application/json" id="public-cases">(.*?)</script>',h,re.S)
    if not model_cases or load_bytes(model_cases.group(1).encode())!=CASES:raise Rejected('HTML cases substitution')
    import html
    embedded_lean=re.search(r'<pre id="lean-source-view">(.*?)</pre>',h,re.S)
    if not embedded_lean or html.unescape(embedded_lean.group(1))!=(root/'ColdChainPublic.lean').read_text(encoding='utf-8'):
        raise Rejected('HTML Lean source substitution')
    if "connect-src 'none'" not in h:raise Rejected('Browser network boundary changed')
    if re.search(r'<script\b[^>]*\bsrc\s*=',h,re.I):raise Rejected('External script')
    # The released model exposes no new input or state compared with v3/v4.
    if INPUT_FIELDS != ('quality','records_complete','authorized','evidence_intact',
                        'upstream_clear','change_before_execution','result_matches'):
        raise Rejected('Unreviewed public input expansion')
    for name in ('index.html','poc.py','ColdChainPublic.lean'):
        text=(root/name).read_text(encoding='utf-8')
        blocked=('api.'+'openai.com','OPENAI_'+'API_KEY','--allow-'+'paid-api',
                 'Bearer'+' ','XMLHttp'+'Request','new '+'WebSocket')
        if any(token in text for token in blocked):
            raise Rejected('External inference/network client in '+name)
    if re.search(r'\b(fetch|sendBeacon|EventSource)\s*\(',h):
        raise Rejected('Unreviewed browser network operation')
    # Exact allowlisting and a reviewed content digest are the principal boundary;
    # token scanning is only a supplemental check, never a zero-leakage proof.
    forbidden=('BEGIN '+'PRIVATE KEY','CCA_PRIVATE_CANARY_'+'DO_NOT_EXPORT','"private_'+'windows"','"private_'+'effects"')
    for name in PUBLIC_FILES:
        text=(root/name).read_text(encoding='utf-8')
        if any(token in text for token in forbidden):raise Rejected('Private marker: '+name)
    files={n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in PUBLIC_FILES}
    return {'status':'PASS','files':files,'file_count':len(files),'evidence_cases':proof['metrics']['cases'],
            'scope':'allowlist-and-content-boundaries;not-IP-legal-clearance'}


def v5_main(argv=None):
    argv=sys.argv[1:] if argv is None else argv
    commands=('model-check','formal-check','audit')
    if not argv or argv[0] not in commands:return main(argv)
    parser=argparse.ArgumentParser(description='Cold-chain public proof and execution verification')
    parser.add_argument('command',choices=commands)
    a=parser.parse_args(argv)
    try:
        result={'model-check':cross_check,'formal-check':formal_check,'audit':public_audit}[a.command]()
        print(json.dumps(result,ensure_ascii=False,indent=2))
        return 0
    except (Rejected,OSError,ValueError,TypeError,KeyError,AssertionError,subprocess.SubprocessError) as exc:
        print('FAIL: '+str(exc),file=sys.stderr);return 2

if __name__=='__main__':raise SystemExit(v5_main())
