import Mathlib.Data.Real.Irrational

/- Problem 2 -/

/- 2.a -/
theorem Thm_2a {P Q : Prop} : P ∧ ¬ Q ∨ P ∧ Q ↔ P := sorry

/- 2.b -/
theorem Thm_2b {U : Type} {A B : Set U} : A = (A \ B) ∪ (A ∩ B) := sorry

/- Problem 3 -/

def isOdd (n : ℕ) : Prop := ∃ m : ℕ, 2 * m + 1 = n

def isPrime (p : ℕ) : Prop := p > 1 ∧ ¬ ∃ m n : ℕ, m > 1 ∧ n > 1 ∧ m * n = p

/- 3.a -/
def sixish (n : ℕ) : Prop := sorry

/- 3.b -/
def prob_3b (Q : ℕ → Prop) : Prop := sorry

/- 3.c -/
def goldbach : Prop := sorry

/- 3.d -/
def prob_3d : Prop := sorry

/- 3.e -/
def R (n : ℕ) : Prop := ∃ b : ℕ, n = 2 * b + 5

def prob_3e : Prop := sorry

/- Prove one of these and delete the other. -/
theorem prob_3e_true : prob_3e := sorry
theorem prob_3e_false : ¬ prob_3e := sorry

/- Problem 4 -/

/- 4.a -/
theorem Q_stronger {n : ℕ} {Q : ℝ → Prop} (hn : n ≥ 1)
  (Q_pred : ∀ x y : ℝ, Q (x * y) → Q x ∨ Q y)
  (xs : Finset.Icc 1 n → ℝ) : Q (∏ i, xs i) → ∃ i, Q (xs i) := sorry

/- 4.b -/
def Q (x : ℝ) : Prop := sorry

/- Prove a lemma about Q here -/

/- 4.c -/
theorem Thm1 {n : ℕ} (hn : n ≥ 1) (xs : Finset.Icc 1 n → { x | Irrational x })
  (h_prod_irrat : Irrational (∏ i, xs i)) : ∃ i, Irrational (xs i) := sorry
