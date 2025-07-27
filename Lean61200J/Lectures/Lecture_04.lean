import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star

/- Definition 1. -/
structure StateMachine (S : Type*) where
  Q : Set S
  q₀ : Q
  T : Q → Set Q

structure DeterministicStateMachine (S : Type*) where
  Q : Set S
  q₀ : Q
  T : Q → Q

instance {S : Type*} : Coe (DeterministicStateMachine S) (StateMachine S) where
  coe (DSM : DeterministicStateMachine S) : StateMachine S := ⟨DSM.Q, DSM.q₀, fun q => {DSM.T q}⟩

namespace StateMachine

variable {S : Type*}
variable (SM : StateMachine S)

/- Definition 1. -/
/- TODO: Add special notation for "exists transition from `s` to `t`" -/
structure FiniteExecution (L : ℕ) where
  /- NOTE: `seq` is only properly defined for `n ≤ L` -/
  seq : ℕ → SM.Q
  start : seq 0 = SM.q₀
  step : ∀ n q, n < L ∧ seq n = q → seq (n + 1) ∈ SM.T q

structure InfiniteExecution where
  seq : ℕ → SM.Q
  start : seq 0 = SM.q₀
  step : ∀ n q, seq n = q → seq (n + 1) ∈ SM.T q

/- Split a finite execution of length `L + 1` by chopping off the last state. -/
def splitExecution {L : ℕ} {SM : StateMachine S}
  (e : SM.FiniteExecution (L + 1)) : SM.FiniteExecution L :=
  ⟨e.seq, e.start, fun n q h => e.step n q ⟨by linarith, h.2⟩⟩

/- Definition 2. -/
def Reachable (r : SM.Q) : Prop :=
  ∃ (L : ℕ) (e : SM.FiniteExecution L) (n : ℕ), n ≤ L ∧ e.seq n = r

/- Definition 3. -/
def Preserved (P : SM.Q → Prop) : Prop :=
  ∀ s, P s → ∀ t ∈ SM.T s, P t

/- Definition 4. -/
def Invariant (P : SM.Q → Prop) : Prop :=
  ∀ r : SM.Q, SM.Reachable r → P r

/- Theorem 2. -/
theorem invariant_principle {SM : StateMachine S} {P : SM.Q → Prop}
  (h_initial : P SM.q₀) (h_preserved : SM.Preserved P) : SM.Invariant P := by
  let Q n : Prop := ∀ (e : SM.FiniteExecution n), ∀ i ≤ n, P (e.seq i)
  have hQ : ∀ n, Q n := by
    intro n
    induction n with
    | zero =>
      intro e
      simp [e.start, h_initial]
    | succ n ih =>
      intro e i hi
      obtain h_lt | h_eq := le_iff_lt_or_eq.1 hi
      · exact ih (splitExecution e) i (by linarith)
      · rw [h_eq]
        have h_Pn : P (e.seq n) := ih (splitExecution e) n (by linarith)
        have h_step : e.seq (n + 1) ∈ SM.T (e.seq n) := e.step n (e.seq n) (by simp)
        exact h_preserved (e.seq n) h_Pn (e.seq (n + 1)) h_step
  intro r ⟨L, e, i, hi, h_seq⟩
  exact h_seq ▸ hQ L e i hi

/- Corollary 3. -/
theorem invariant_false_unreachable {P : SM.Q → Prop} {s : SM.Q}
  (h_invariant : SM.Invariant P) (h_not_P : ¬ P s) : ¬ SM.Reachable s := by
  by_contra h_reachable
  specialize h_invariant s h_reachable
  contradiction

/- Definition 5. -/
def FinalState (q : SM.Q) : Prop := SM.T q = ∅

/- Definition 6. -/
def Terminates : Prop := ¬ Nonempty SM.InfiniteExecution

/- Definition 7. -/
def DerivedVariable (T : Type*) := SM.Q → T

/- Definition 8. -/
def StrictlyDecreasingDV {T : Type*} [LT T] (f : SM.DerivedVariable T) : Prop :=
  ∀ s t : SM.Q, t ∈ SM.T s → f t < f s

def WeaklyDecreasingDV {T : Type*} [LE T] (f : SM.DerivedVariable T) : Prop :=
  ∀ s t : SM.Q, t ∈ SM.T s → f t ≤ f s

/- Theorem 4. -/
theorem strictly_decreasing_nat_terminates
  (f : SM.DerivedVariable ℕ)
  (h_f_sd : SM.StrictlyDecreasingDV f) : SM.Terminates := by
  by_contra h_inf
  unfold Terminates at h_inf
  push_neg at h_inf
  have e : SM.InfiniteExecution := Classical.choice h_inf
  let F n := f (e.seq n)
  have h_descending : ∀ n, F (n + 1) < F n := by
    intro n
    apply h_f_sd
    exact e.step n (e.seq n) rfl
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ F (r := LT.lt)
  specialize h_descending n
  contradiction

end StateMachine

/- Counter example -/
def Counter : StateMachine ℕ :=
  ⟨Set.univ, ⟨0, by simp⟩, fun n ↦ {⟨n + 1, by simp⟩}⟩

example : ¬ Counter.Terminates := by
  unfold StateMachine.Terminates
  push_neg
  refine ⟨fun n ↦ ⟨n, ?_⟩, ?_, ?_⟩ <;> simp [Counter]
