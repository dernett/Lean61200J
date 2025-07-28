import Lean61200J.Lectures.Lecture_04
import Mathlib.Data.Nat.Log

abbrev S := ℕ × ℕ × ℕ

def DetIntegerMulSM (x y : ℕ) : DetStateMachine S :=
  ⟨⟨x, y, 0⟩, T⟩
  where T : S → Option S
    | (_, 0, _) => none
    | (r, s, a) =>
      if s % 2 = 0 then
        (2*r, s/2, a)
      else
        (2*r, (s-1)/2, a + r)

@[simp]
def IntegerMulSM (x y : ℕ) : StateMachine S := DetIntegerMulSM x y

/- Problem 3.a -/
partial def runWithDisplay {Q : Type*} [ToString Q] (DSM : DetStateMachine Q) : IO Unit :=
  let rec run q := do
    IO.println q
    match DSM.T q with
    | none => IO.println "Done!"
    | some s => run s
  run DSM.q₀

#eval runWithDisplay (DetIntegerMulSM 5 22)

def P (x y : ℕ) : S → Prop
  | ⟨r, s, a⟩ => r * s + a = x * y

def correct (x y : ℕ) : S → Prop
  | ⟨_, _, a⟩ => a = x * y

section

variable {x y : ℕ}

/- Problem 3.b -/
theorem mul_sm_preserved : (IntegerMulSM x y).Preserved (P x y) := by
  intro q h t ht
  let ⟨r, s, a⟩ := q
  simp [P] at h
  simp [DetIntegerMulSM, DetIntegerMulSM.T] at ht
  split at ht
  · contradiction
  · next r s a h_s_nz h_eq =>
    simp at h_eq
    split_ifs at ht <;> simp at ht <;> simp [← ht, P]
    · next h_even =>
      replace h_even : 2 ∣ s := Nat.dvd_of_mod_eq_zero h_even
      simp [← h, h_eq]
      nth_rewrite 2 [← Nat.div_mul_cancel h_even]
      ring
    · next h_odd =>
      replace : (s - 1) % 2 = 0 := by grind
      replace : 2 ∣ (s - 1) := Nat.dvd_of_mod_eq_zero this
      simp [← h, h_eq]
      rw [mul_comm 2 r, mul_assoc, Nat.mul_div_cancel' this]
      cases s
      · contradiction
      · simp; ring

theorem mul_sm_invariant : (IntegerMulSM x y).Invariant (P x y) := by
  apply StateMachine.invariant_principle
  · simp [DetIntegerMulSM, P]
  · exact mul_sm_preserved

/- Problem 3.c -/
theorem mul_sm_final_states : (IntegerMulSM x y).FinalStates = { (_, s, _) : S | s = 0 } := by
  simp [StateMachine.FinalStates, StateMachine.FinalState,
        DetIntegerMulSM, DetIntegerMulSM.T]
  ext
  simp
  split <;> simp
  split_ifs <;> simp <;> trivial

/- Problem 3.d -/
theorem mul_sm_final_state_correct :
  ∀ q, (IntegerMulSM x y).Reachable q → (IntegerMulSM x y).FinalState q → correct x y q := by
  intro q h_reachable h_final
  let ⟨r, s, a⟩ := q
  have h_s_zero : s = 0 := by
    change (r, s, a) ∈ (IntegerMulSM x y).FinalStates at h_final
    rw [mul_sm_final_states] at h_final
    simp at h_final; trivial
  have h_P : P x y (r, s, a) := mul_sm_invariant (r, s, a) h_reachable
  simp [h_s_zero, P] at h_P
  simp [correct, h_P]

def bitcount (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

#eval bitcount 5
#eval bitcount 1
#eval bitcount 0

def BitcountDV : (IntegerMulSM x y).DerivedVariable ℕ
  | ⟨_, s, _⟩ => bitcount s

/- Problem 3.e -/
theorem bitcount_strictly_decreasing {x y : ℕ} :
  (IntegerMulSM x y).StrictlyDecreasingDV BitcountDV := by
  unfold StateMachine.StrictlyDecreasingDV
  intro s t h_trans
  let ⟨r, s, a⟩ := t
  simp [DetIntegerMulSM, DetIntegerMulSM.T] at h_trans
  split at h_trans
  · contradiction
  · next r₂ s₂ a₂ h_s₂ =>
    simp [BitcountDV]
    split_ifs at h_trans <;> simp at h_trans
    -- TODO: Duplication
    · obtain ⟨_, h_s, _⟩ := h_trans
      simp [← h_s, bitcount]
      nth_rewrite 2 [Nat.clog_of_two_le (by decide)]
      · simp
      · grind
    · obtain ⟨_, h_s, _⟩ := h_trans
      simp [← h_s, bitcount]
      nth_rewrite 2 [Nat.clog_of_two_le (by decide)]
      · have : (s₂ - 1) / 2 = s₂ / 2 := by grind
        simp [this]
      · grind

theorem mul_sm_terminates : (IntegerMulSM x y).Terminates :=
  (IntegerMulSM x y).strictly_decreasing_nat_terminates BitcountDV bitcount_strictly_decreasing

/- Problem 3.f -/
theorem mul_sm_time_bound (L : ℕ) (e : (IntegerMulSM x y).FiniteExecution L) : L ≤ bitcount y := by
  by_contra h
  push_neg at h
  have h_ind : ∀ n ≤ bitcount y, n + @BitcountDV x y (e.seq n) ≤ bitcount y := by
    intro n hn
    induction n with
    | zero =>
      simp [e.start, BitcountDV, DetIntegerMulSM]
    | succ n ih =>
      specialize ih (by linarith)
      have : BitcountDV (e.seq (n + 1)) < BitcountDV (e.seq n) :=
        (IntegerMulSM x y).strictly_decreasing_finite_exec_succ
          (by linarith)
          bitcount_strictly_decreasing
      calc n + 1 + @BitcountDV x y (e.seq (n + 1))
          ≤ n + @BitcountDV x y (e.seq n) := by linarith
        _ ≤ bitcount y := ih
  have h_y : @BitcountDV x y (e.seq (bitcount y)) = 0 := by
    specialize h_ind (bitcount y) (by linarith)
    linarith
  have h_dec : BitcountDV (e.seq (bitcount y + 1)) < BitcountDV (e.seq (bitcount y)) :=
    (IntegerMulSM x y).strictly_decreasing_finite_exec_succ
      (by linarith)
      bitcount_strictly_decreasing
  rw [h_y] at h_dec
  norm_num at h_dec

end
