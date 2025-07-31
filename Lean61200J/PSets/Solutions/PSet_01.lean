import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.Irrational

/- Problem 2 -/

/- 2.a -/
theorem problem_2a {P Q : Prop} : P ∧ ¬ Q ∨ P ∧ Q ↔ P := by
  tauto

/- 2.b -/
theorem problem_2b {U : Type} {A B : Set U} : A = (A \ B) ∪ (A ∩ B) := by
  ext x
  constructor
  · intro h_A
    by_cases h_B : x ∈ B
    · right
      exact ⟨h_A, h_B⟩
    · left
      exact ⟨h_A, h_B⟩
  · rintro (h₁ | h₂)
    · exact h₁.1
    · exact h₂.1

/- Problem 3 -/

def IsOdd (n : ℕ) : Prop := ∃ m : ℕ, 2 * m + 1 = n

def IsPrime (p : ℕ) : Prop := p > 1 ∧ ¬ ∃ m n : ℕ, m > 1 ∧ n > 1 ∧ m * n = p

/- 3.a -/
def Sixish (n : ℕ) : Prop := ∃ k j : ℕ, n = 6 * 10^k + j ∧ j < 10^k

/- 3.b -/
def Problem3b {Q : ℕ → Prop} : Prop := { n : ℕ | Q n }.ncard == 2

/- 3.c -/
def Goldbach : Prop := ∀ n : ℕ, n > 2 ∧ ¬ IsOdd n → ∃ p q, IsPrime p ∧ IsPrime q ∧ n = p + q

/- 3.d -/
def Problem3d : Prop := ∀ p, IsPrime p ∧ p > 100 → Sixish p

/- 3.e -/
def R (n : ℕ) : Prop := ∃ b : ℕ, n = 2 * b + 5

def Problem3e : Prop := ∀ n, R n ↔ IsOdd n

/- Prove one of these and delete the other. -/
theorem problem_3e_false : ¬ Problem3e := by
  unfold Problem3e
  push_neg
  use 1
  right
  exact ⟨by grind [R], by use 0⟩

/- Problem 4 -/

/- 4.a -/
theorem Q_stronger {n : ℕ} {Q : ℝ → Prop} (hn : 1 ≤ n)
    (Q_pred : ∀ x y : ℝ, Q (x * y) → Q x ∨ Q y) (xs : ℕ → ℝ) :
    Q (∏ i ∈ Finset.Icc 1 n, xs i) → ∃ i, Q (xs i) := by
  intro h
  -- Start the induction at `n = 1`
  induction n, hn using Nat.le_induction with
  | base => aesop
  | succ n hmn ih =>
    rw [Finset.prod_Icc_succ_top (by linarith)] at h
    apply Q_pred at h
    by_cases h_last : Q (xs (n + 1))
    · use n + 1
    · exact ih (Or.resolve_right h h_last)

/- 4.b -/
def Q (x : ℝ) : Prop := Irrational x

lemma irrational_mul_or : ∀ x y : ℝ, Irrational (x * y) → Irrational x ∨ Irrational y := by
  intro x y h
  by_cases h_x : Irrational x
  · left
    exact h_x
  · right
    by_contra h_y
    simp [Irrational] at h_x h_y
    rcases h_x with ⟨q, rfl⟩
    rcases h_y with ⟨r, rfl⟩
    simp [Irrational] at h
    specialize h (q * r)
    push_cast at h
    contradiction

/- 4.c -/
theorem prod_irrational_exists {n : ℕ} (hn : n ≥ 1) (xs : ℕ → { x : ℝ | Irrational x })
    (h_prod_irrational : Irrational (∏ i ∈ Finset.Icc 1 n, xs i)) : ∃ i, Irrational (xs i) := by
  by_contra h
  have h_contra : ∃ i, Irrational (xs i) := Q_stronger hn irrational_mul_or _ h_prod_irrational
  contradiction
