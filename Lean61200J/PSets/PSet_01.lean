import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.Irrational

/- Problem 2 -/

/- 2.a -/
theorem problem_2a {P Q : Prop} : P ∧ ¬ Q ∨ P ∧ Q ↔ P := sorry

/- 2.b -/
theorem problem_2b {U : Type} {A B : Set U} : A = (A \ B) ∪ (A ∩ B) := sorry

/- Problem 3 -/

def IsOdd (n : ℕ) : Prop := ∃ m : ℕ, 2 * m + 1 = n

def IsPrime (p : ℕ) : Prop := p > 1 ∧ ¬ ∃ m n : ℕ, m > 1 ∧ n > 1 ∧ m * n = p

/- 3.a -/
def Sixish (n : ℕ) : Prop := sorry

/- 3.b -/
def Problem3b {Q : ℕ → Prop} : Prop := sorry

/- 3.c -/
def Goldbach : Prop := sorry

/- 3.d -/
def Problem3d : Prop := sorry

/- 3.e -/
def R (n : ℕ) : Prop := ∃ b : ℕ, n = 2 * b + 5

def Problem3e : Prop := ∀ n, R n ↔ IsOdd n

/- Prove one of these and delete the other. -/
theorem problem_3e_true : Problem3e := sorry
theorem problem_3e_false : ¬ Problem3e := sorry

/- Problem 4 -/

/- 4.a -/
theorem Q_stronger {n : ℕ} {Q : ℝ → Prop} (hn : 1 ≤ n)
    (Q_pred : ∀ x y : ℝ, Q (x * y) → Q x ∨ Q y) (xs : ℕ → ℝ) :
    Q (∏ i ∈ Finset.Icc 1 n, xs i) → ∃ i, Q (xs i) := sorry

/- 4.b -/
def Q (x : ℝ) : Prop := sorry

/- Prove a lemma about Q here -/

/- 4.c -/
theorem prod_irrational_exists {n : ℕ} (hn : n ≥ 1) (xs : ℕ → { x : ℝ | Irrational x })
    (h_prod_irrational : Irrational (∏ i ∈ Finset.Icc 1 n, xs i)) : ∃ i, Irrational (xs i) := sorry
