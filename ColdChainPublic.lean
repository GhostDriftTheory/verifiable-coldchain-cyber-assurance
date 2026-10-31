import Std

/-!
# Cold-chain public reference model — formal boundary
Only the seven coarse conditions and two state bits already exposed by v3 are modeled.
This is NOT the private implementation, a sensor-authenticity proof, or a WMS proof.
Input decoding, cryptography, JavaScript/Python runtimes, network and physical effects
are outside this model. Concrete implementation comparisons are a separate check.
No proprietary thresholds, raw logs, key-management or liability logic is introduced.
Recheck: `python poc.py formal-check` (requires the pinned Lean toolchain).
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 0

namespace ColdChainPublic
inductive Quality where
  | ok | review | fail
  deriving DecidableEq, BEq, Repr
inductive Status where
  | denied | hold | released | quarantined
  deriving DecidableEq, BEq, Repr
inductive Stage where
  | precheck | recheck | complete | postcheck
  deriving DecidableEq, BEq, Repr
inductive Reason where
  | quarantineLock | alreadyExecuted | authorityMismatch | evidenceMismatch
  | qualityFailed | recordsMissing | upstreamUnresolved | qualityReview
  | conditionsChanged | resultMismatch
  deriving DecidableEq, BEq, Repr
structure Input where
  quality : Quality
  records : Bool
  authorized : Bool
  evidence : Bool
  upstream : Bool
  changed : Bool
  resultMatches : Bool
  deriving DecidableEq, Repr
structure State where
  consumed : Bool
  quarantined : Bool
  deriving DecidableEq, Repr
structure Outcome where
  status : Status
  stage : Stage
  reasons : List Reason
  calls : Nat
  effects : Nat
  confirmed : Nat
  quarantined : Bool
  next : State
  deriving DecidableEq, Repr

def initial : State := ⟨false, false⟩
def hard (x : Input) : List Reason :=
  (if x.authorized then [] else [.authorityMismatch]) ++
  (if x.evidence then [] else [.evidenceMismatch]) ++
  (if x.quality == .fail then [.qualityFailed] else [])
def soft (x : Input) : List Reason :=
  (if x.records then [] else [.recordsMissing]) ++
  (if x.upstream then [] else [.upstreamUnresolved]) ++
  (if x.quality == .review then [.qualityReview] else [])
def stopped (s : State) (status : Status) (stage : Stage) (rs : List Reason) : Outcome :=
  ⟨status, stage, rs, 0, 0, 0, false, s⟩
def step (s : State) (x : Input) : Outcome :=
  if s.quarantined then stopped s .denied .precheck [.quarantineLock]
  else if s.consumed then stopped s .denied .precheck [.alreadyExecuted]
  else if !(hard x).isEmpty then stopped s .denied .precheck (hard x)
  else if !(soft x).isEmpty then stopped s .hold .precheck (soft x)
  else if x.changed then stopped s .denied .recheck [.conditionsChanged]
  else if x.resultMatches then ⟨.released, .complete, [], 1, 1, 1, false, ⟨true, s.quarantined⟩⟩
  else ⟨.quarantined, .postcheck, [.resultMismatch], 1, 1, 0, true, ⟨true, true⟩⟩

def eligible (s : State) (x : Input) : Bool :=
  !s.consumed && !s.quarantined && (x.quality == .ok) &&
  x.records && x.authorized && x.evidence && x.upstream && !x.changed

/-- Universal local safety relation; no external oracle or native_decide. -/
theorem step_properties (s : State) (x : Input) :
  ((step s x).calls = 1 ↔ eligible s x = true) ∧
  ((step s x).calls = 0 ∨ (step s x).calls = 1) ∧
  ((step s x).effects = (step s x).calls) ∧
  ((step s x).confirmed = 1 ↔ (step s x).status = .released) ∧
  ((step s x).confirmed = 0 ∨ (step s x).confirmed = 1) ∧
  ((step s x).status = .released → x.resultMatches = true) ∧
  ((step s x).calls = 1 → x.resultMatches = false → (step s x).status = .quarantined) ∧
  ((step s x).status = .denied → (step s x).effects = 0) ∧
  ((step s x).status = .hold → (step s x).effects = 0) ∧
  (x.authorized = false → (step s x).status = .denied) ∧
  (x.evidence = false → (step s x).status = .denied) ∧
  (x.quality = .fail → (step s x).status = .denied) ∧
  (x.records = false → (step s x).calls = 0) ∧
  (x.upstream = false → (step s x).calls = 0) ∧
  (x.quality = .review → (step s x).calls = 0) ∧
  (x.changed = true → (step s x).calls = 0) ∧
  (s.consumed = true → (step s x).calls = 0) ∧
  (s.quarantined = true → (step s x).calls = 0) ∧
  (s.consumed = true → (step s x).next.consumed = true) ∧
  (s.quarantined = true → (step s x).next.quarantined = true) ∧
  ((step s x).calls = 1 → (step s x).next.consumed = true) ∧
  ((step s x).calls = 1 → x.resultMatches = false → (step s x).next.quarantined = true) ∧
  ((step s x).calls = 0 → (step s x).next = s) ∧
  ((step s x).status = .quarantined → (step s x).confirmed = 0) ∧
  ((step s x).status = .released → x.quality = .ok) ∧
  (eligible s x = true → x.resultMatches = true → (step s x).status = .released) ∧
  ((step s x).status = .quarantined → (step s x).effects = 1) ∧
  ((s.quarantined = true → s.consumed = true) → ((step s x).next.quarantined = true → (step s x).next.consumed = true)) := by
  cases s with
  | mk c z =>
    cases x with
    | mk q r a e u d m =>
      cases c <;> cases z <;> cases q <;> cases r <;> cases a <;>
        cases e <;> cases u <;> cases d <;> cases m <;> decide

theorem calls_iff_eligible (s : State) (x : Input) :
    (step s x).calls = 1 ↔ eligible s x = true :=
  (step_properties s x).1

theorem calls_zero_or_one (s : State) (x : Input) :
    (step s x).calls = 0 ∨ (step s x).calls = 1 :=
  (step_properties s x).2.1

theorem effects_eq_calls (s : State) (x : Input) :
    (step s x).effects = (step s x).calls :=
  (step_properties s x).2.2.1

theorem confirmed_iff_released (s : State) (x : Input) :
    (step s x).confirmed = 1 ↔ (step s x).status = .released :=
  (step_properties s x).2.2.2.1

theorem confirmed_zero_or_one (s : State) (x : Input) :
    (step s x).confirmed = 0 ∨ (step s x).confirmed = 1 :=
  (step_properties s x).2.2.2.2.1

theorem released_has_matching_result (s : State) (x : Input) :
    (step s x).status = .released → x.resultMatches = true :=
  (step_properties s x).2.2.2.2.2.1

theorem called_mismatch_is_quarantined (s : State) (x : Input) :
    (step s x).calls = 1 → x.resultMatches = false → (step s x).status = .quarantined :=
  (step_properties s x).2.2.2.2.2.2.1

theorem denied_no_effect (s : State) (x : Input) :
    (step s x).status = .denied → (step s x).effects = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.1

theorem hold_no_effect (s : State) (x : Input) :
    (step s x).status = .hold → (step s x).effects = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.2.1

theorem unauthorized_denied (s : State) (x : Input) :
    x.authorized = false → (step s x).status = .denied :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.1

theorem bad_evidence_denied (s : State) (x : Input) :
    x.evidence = false → (step s x).status = .denied :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.1

theorem failed_quality_denied (s : State) (x : Input) :
    x.quality = .fail → (step s x).status = .denied :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.1

theorem missing_records_no_call (s : State) (x : Input) :
    x.records = false → (step s x).calls = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem upstream_unresolved_no_call (s : State) (x : Input) :
    x.upstream = false → (step s x).calls = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem review_quality_no_call (s : State) (x : Input) :
    x.quality = .review → (step s x).calls = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem changed_conditions_no_call (s : State) (x : Input) :
    x.changed = true → (step s x).calls = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem consumed_no_call (s : State) (x : Input) :
    s.consumed = true → (step s x).calls = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem quarantine_no_call (s : State) (x : Input) :
    s.quarantined = true → (step s x).calls = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem consumed_monotone (s : State) (x : Input) :
    s.consumed = true → (step s x).next.consumed = true :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem quarantine_monotone (s : State) (x : Input) :
    s.quarantined = true → (step s x).next.quarantined = true :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem called_consumes (s : State) (x : Input) :
    (step s x).calls = 1 → (step s x).next.consumed = true :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mismatch_locks (s : State) (x : Input) :
    (step s x).calls = 1 → x.resultMatches = false → (step s x).next.quarantined = true :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem no_call_preserves_state (s : State) (x : Input) :
    (step s x).calls = 0 → (step s x).next = s :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem quarantine_is_not_confirmed (s : State) (x : Input) :
    (step s x).status = .quarantined → (step s x).confirmed = 0 :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem release_requires_quality_ok (s : State) (x : Input) :
    (step s x).status = .released → x.quality = .ok :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem eligible_matching_releases (s : State) (x : Input) :
    eligible s x = true → x.resultMatches = true → (step s x).status = .released :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem quarantine_has_prior_effect (s : State) (x : Input) :
    (step s x).status = .quarantined → (step s x).effects = 1 :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem initial_valid_state_preserved (s : State) (x : Input) :
    (s.quarantined = true → s.consumed = true) → ((step s x).next.quarantined = true → (step s x).next.consumed = true) :=
  (step_properties s x).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Number of simulated effects over an arbitrary finite sequence. -/
def totalEffects (s : State) : List Input → Nat
  | [] => 0
  | x :: xs => (step s x).effects + totalEffects (step s x).next xs

theorem consumed_trace_zero (xs : List Input) (s : State)
    (h : s.consumed = true) : totalEffects s xs = 0 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hz := consumed_no_call s x h
    have hn := consumed_monotone s x h
    simp only [totalEffects, effects_eq_calls, hz, Nat.zero_add]
    exact ih (step s x).next hn

theorem quarantined_trace_zero (xs : List Input) (s : State)
    (h : s.quarantined = true) : totalEffects s xs = 0 := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hz := quarantine_no_call s x h
    have hn := quarantine_monotone s x h
    simp only [totalEffects, effects_eq_calls, hz, Nat.zero_add]
    exact ih (step s x).next hn

/-- At most one simulated effect for the same handoff, at every trace length. -/
theorem trace_at_most_once (xs : List Input) (s : State) : totalEffects s xs ≤ 1 := by
  induction xs generalizing s with
  | nil => simp [totalEffects]
  | cons x xs ih =>
    cases calls_zero_or_one s x with
    | inl hz =>
      simp only [totalEffects, effects_eq_calls, hz, Nat.zero_add]
      exact ih (step s x).next
    | inr ho =>
      have hn := called_consumes s x ho
      have hz := consumed_trace_zero xs (step s x).next hn
      simp only [totalEffects, effects_eq_calls, ho, hz]
      decide

/-- Any nonempty replay after a successful call has no further effect. -/
theorem replay_cannot_repeat (s : State) (x : Input) (xs : List Input)
    (h : (step s x).calls = 1) : totalEffects (step s x).next xs = 0 :=
  consumed_trace_zero xs (step s x).next (called_consumes s x h)

/-- Holding alone does not consume the request, so corrected evidence can be retried. -/
theorem hold_does_not_consume (s : State) (x : Input)
    (h : (step s x).status = .hold) : (step s x).next = s := by
  apply no_call_preserves_state s x
  rw [← effects_eq_calls s x]
  exact hold_no_effect s x h

def normal : Input := ⟨.ok, true, true, true, true, false, true⟩
theorem normal_progress : (step initial normal).status = .released := by decide
theorem evidence_completion_progress :
    (step (step initial { normal with records := false }).next normal).status = .released := by decide
theorem mismatch_then_replay_stops :
    (step (step initial { normal with resultMatches := false }).next normal).calls = 0 := by decide

def statusCode : Status → Nat
  | .denied => 0 | .hold => 1 | .released => 2 | .quarantined => 3
def stageCode : Stage → Nat
  | .precheck => 0 | .recheck => 1 | .complete => 2 | .postcheck => 3
def reasonCode : Reason → Nat
  | .quarantineLock => 0 | .alreadyExecuted => 1 | .authorityMismatch => 2
  | .evidenceMismatch => 3 | .qualityFailed => 4 | .recordsMissing => 5
  | .upstreamUnresolved => 6 | .qualityReview => 7 | .conditionsChanged => 8
  | .resultMismatch => 9
def bit (b : Bool) : Nat := if b then 1 else 0
/-- The whole observable result, including reason order and next state, not only PASS. -/
def fingerprint (s : State) (x : Input) : List Nat :=
  let y := step s x
  [statusCode y.status, stageCode y.stage, y.calls, y.effects, y.confirmed,
   bit y.quarantined, bit y.next.consumed, bit y.next.quarantined] ++
  y.reasons.map reasonCode

#print axioms step_properties
#print axioms trace_at_most_once
#print axioms replay_cannot_repeat
#print axioms evidence_completion_progress
end ColdChainPublic
