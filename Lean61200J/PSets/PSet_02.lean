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
partial def runWithDisplay {Q : Type*} [ToString Q] (DSM : DetStateMachine Q) : IO Unit := sorry

/-
#eval runWithDisplay (DetIntegerMulSM 5 22)
-/

def P (x y : ℕ) : S → Prop
  | ⟨r, s, a⟩ => r * s + a = x * y

def correct (x y : ℕ) : S → Prop
  | ⟨_, _, a⟩ => a = x * y

section

variable {x y : ℕ}

/- Problem 3.b -/
theorem mul_sm_preserved : (IntegerMulSM x y).Preserved (P x y) := sorry

theorem mul_sm_invariant : (IntegerMulSM x y).Invariant (P x y) := sorry

/- Problem 3.c -/
theorem mul_sm_final_states : (IntegerMulSM x y).FinalStates = { (_, s, _) : S | s = 0 } := sorry

/- Problem 3.d -/
theorem mul_sm_final_state_correct :
  ∀ q, (IntegerMulSM x y).Reachable q → (IntegerMulSM x y).FinalState q → correct x y q := sorry

def bitcount (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

#eval bitcount 5
#eval bitcount 1
#eval bitcount 0

def BitcountDV : (IntegerMulSM x y).DerivedVariable ℕ
  | ⟨_, s, _⟩ => bitcount s

/- Problem 3.e -/
theorem bitcount_strictly_decreasing {x y : ℕ} :
  (IntegerMulSM x y).StrictlyDecreasingDV BitcountDV := sorry

theorem mul_sm_terminates : (IntegerMulSM x y).Terminates := sorry

/- Problem 3.f -/
theorem mul_sm_time_bound (L : ℕ) (e : (IntegerMulSM x y).FiniteExecution L) : L ≤ bitcount y :=
  sorry

end
