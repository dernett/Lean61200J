import Mathlib

/- Section 1. Logical Deduction -/
section

variable (P Q R : Prop)

/- Modus ponens -/
example : (P → Q) → P → Q := fun hpq hp ↦ hpq hp
example : (P → Q) → P → Q := by
  intro hpq hp
  exact hpq hp

/- Modus tollens -/
example : (P → Q) → ¬ Q → ¬ P := fun hpq hnq hp ↦ hnq (hpq hp)
example : (P → Q) → ¬ Q → ¬ P := by
  intro hpq hnq hp
  exact hnq (hpq hp)

example : (P → Q) → (Q → R) → (P → R) := fun hpq hqr hp ↦ hqr (hpq hp)
example : (P → Q) → (Q → R) → (P → R) := by
  intro hpq hqr hp
  exact hqr (hpq hp)

example : (¬ P → False) → P := by
  by_cases h : P
  · exact fun _ ↦ h
  · intro hnp
    exfalso
    exact hnp h

end
/- Section 2. Fundamental proof techniques -/
section

/- Proving Existence -/
example : ∃ n : ℕ, n ≥ 10 ∧ Nat.Prime n := by
  -- We’ll show that `n = 17` satisfes the required condition.
  use 17
  -- This is true because 17 is a prime number and `17 ≥ 10`.
  exact ⟨by decide, by decide⟩

/- Proving Universality -/
example : ∀ x : ℝ, x ^ 2 - 6 * x > -10 := by
  -- Suppose `x` is an arbitrary real number.
  intro x
  -- Then `x^2 − 6*x + 9 = (x−3)^2`
  have h_square : x ^ 2 - 6 * x + 9 = (x - 3) ^ 2 := by ring
  -- which is ≥ 0 because the square of every real number is nonnegative
  have h_pos : (x - 3) ^ 2 ≥ 0 := sq_nonneg (x - 3)
  calc x ^ 2 - 6 * x
        = (x - 3) ^ 2 - 9 := by rw [← h_square]; simp
      _ ≥ -9 := by linarith -- (le_add_iff_nonneg_left _).2 h_pos
      _ > -10 := by norm_num

/- Proof of an Implication: Direct Method -/
example {n : ℤ} (h_mul_10 : 10 ∣ n) : 2 ∣ n := by
  -- Assume `n` is a multiple of 10; in other words, `n = 10k` for some integer `k`.
  obtain ⟨k, hk⟩ := h_mul_10
  -- This means `n = 2*(5*k)`
  use 5 * k
  -- and therefore `n` is equal to 2 times an integer (namely, `5*k`)
  rw [hk]; ring

/- Proof of an Implication: Contrapositive -/
lemma even_square_even {n : ℤ} : Even (n ^ 2) → Even n := by
  -- The desired theorem is equivalent to its contrapositive
  -- (`n` is odd) implies (`n^2` is odd), so we’ll prove this implication directly.
  rw [← not_imp_not]
  simp only [Int.not_even_iff_odd]
  -- Assume `n` is odd, and we’ll prove that `n^2` is also odd.
  intro h_n_odd
  -- Since `n` is odd, we know `n = 2*k+1` for some integer k
  obtain ⟨k, hn⟩ := h_n_odd
  -- Then `n^2 = (2*k+1)^2 = 4*k^2+4*k+1 = 2*(2*k^2 + 2*k) + 1`,
  -- which is one more than a multiple of 2, as required.
  use (2 * k ^ 2 + 2 * k)
  calc n ^ 2
        = (2 * k + 1) ^ 2 := by rw [hn]
      _ = 4 * (k ^ 2) + 4 * k + 1 := by ring
      _ = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring

end
/- Section 3. Proof by Contradiction -/
section

theorem Thm1 : Irrational √2 := by
  unfold Irrational
  -- Assume for sake of contradiction that 2 ∈ Q.
  by_contra h_exists_rat
  rw [Set.mem_range] at h_exists_rat
  obtain ⟨r, h_rat⟩ := h_exists_rat
  -- let a, b ∈ Z have no common divisors
  let a : ℤ := r.num
  let b : ℤ := r.den
  have gcd_eq_one : Int.gcd a b = 1 := r.reduced

  replace : a / b = √2 := by
    rw [← h_rat]
    norm_cast
    exact Rat.divInt_self r
  replace : a = b * √2 := by field_simp at this; linarith
  replace : a ^ 2 = 2 * b ^ 2 := by
    rify
    apply congrArg (· ^ 2) at this
    ring_nf at this; simp at this
    linarith

  -- This tells us that `a^2` is even.
  have a_square_even : Even (a ^ 2) := by use b ^ 2; rw [this]; ring
  -- By our theorem above, `a` itself must be even,
  have a_even : Even a := even_square_even a_square_even
  -- so we can write `a = 2c` for some integer c.
  obtain ⟨c, ha⟩ := a_even

  replace : (2 * c) ^ 2 = 2 * b ^ 2:= by rw [ha] at this; linarith
  replace : 4 * c ^ 2 = 2 * b ^ 2 := by ring_nf at this; linarith
  replace : 2 * c ^ 2 = b ^ 2 := by linarith

  -- This shows `b^2` is even, so with our lemma again, `b` itself is even.
  have b_square_even : Even (b ^ 2) := by use c ^ 2; rw [← this]; ring
  have b_even : Even b := even_square_even b_square_even
  obtain ⟨d, hb⟩ := b_even

  -- Now a and b share a factor (2).
  have two_dvd_a : 2 ∣ a := by use c; rw [ha]; ring
  have two_dvd_b : 2 ∣ b := by use d; rw [hb]; ring
  have two_dvd_gcd : (2 : ℤ) ∣ Int.gcd a b := dvd_gcd two_dvd_a two_dvd_b
  have two_dvd_one : (2 : ℤ) ∣ 1 := by rwa [gcd_eq_one] at two_dvd_gcd
  norm_num at two_dvd_one

end
/- Section 5. Proof by Induction -/
section

#check Nat.mul_div_cancel

-- We sum up rationals instead of Nats to make the algebra simpler
theorem Thm2 : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      ring

/- Strengthening the Induction Hypothesis -/
/- TODO: Formalize what it means for a grid to be tiled with L-trominoes.  -/

end
