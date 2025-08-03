import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Rify

theorem geo_sum {x : ℝ} (hx : x ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, x ^ k = (1 - x ^ n) / (1 - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 - x ≠ 0 := by grind
    field_simp
    ring

theorem sum_squares (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, k ^ 2 = (1/3 * n^3 + 1/2 * n^2 + 1/6 * n : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast at *
    rw [Finset.sum_Icc_succ_top (by simp), ih]
    field_simp
    ring

example (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc i n, j =
  ((n * (n + 1) * (2 * n + 1)) / 6 : ℚ) := by
  have :=
    calc
      ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc i n, j
        = ∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 j, j := by
          apply Finset.sum_comm'
          intro x y
          simp; constructor <;> intros <;> split_ands <;> linarith
      _ = ∑ j ∈ Finset.Icc 1 n, j ^ 2 := by
        simp [Finset.sum_const, Nat.card_Icc, Nat.pow_two]
  rw [this, sum_squares]
  field_simp
  ring

open Finset in
example (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ Icc 1 n, j * 2 ^ j = (n - 1) * 2 ^ (n + 1) + 2 := by
  qify
  rw [Nat.cast_sub (by linarith)]
  exact calc
    ∑ j ∈ Icc 1 n, (j * 2 ^ j : ℚ)
      = ∑ i ∈ Icc 1 n, ∑ j ∈ Icc i n, 2 ^ j := by
      conv =>
        lhs; arg 2; intro j;
        conv => arg 1; rw [show j = ∑ i ∈ Icc 1 j, (1 : ℚ) from by simp [Finset.sum_const]]
        rw [Finset.sum_mul, one_mul]
      apply Finset.sum_comm'
      intro x y
      simp; constructor <;> intros <;> split_ands <;> linarith
    _ = ∑ i ∈ Icc 1 n, (2 ^ (n + 1) - 2 ^ i) := by
      -- TODO: This could probably be better
      conv =>
        lhs;
        rw [← Finset.sum_attach]
        conv =>
          arg 2; intro i
          rw [← Ico_add_one_right_eq_Icc,
              geom_sum_Ico (by trivial) (by aesop (add safe (by linarith)))]
        rw [Finset.sum_attach (Icc 1 n) (fun i => (2 ^ (n + 1) - 2 ^ i) / (2 - 1))]
      ring_nf
    _ = ∑ i ∈ Icc 1 n, 2 ^ (n + 1) - ∑ i ∈ Icc 1 n, 2 ^ i := by
      simp [sum_sub_distrib]
    _ = n * 2 ^ (n + 1) - 2 ^ (n + 1) + 2 := by
      simp [Finset.sum_const]
      rw [← Ico_add_one_right_eq_Icc, geom_sum_Ico (by trivial) (by linarith)]
      ring
    _ = (n - 1) * 2 ^ (n + 1) + 2 := by
      field_simp
      ring

open MeasureTheory Set Filter Function

theorem integral_congr_Ico {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b) (h : EqOn f g (Ico a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  simp [intervalIntegral.integral_of_le hab,
        ←setIntegral_congr_set Ico_ae_eq_Ioc,
        setIntegral_congr_fun measurableSet_Ico h]

theorem integral_congr_Ioc {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b) (h : EqOn f g (Ioc a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  simp [intervalIntegral.integral_of_le hab,
        setIntegral_congr_fun measurableSet_Ioc h]

theorem floor_Icc {a b : ℕ} {x : ℝ} (h : x ∈ Icc ↑a ↑b) :
    ↑(Nat.floor x) ∈ Icc (↑a : ℝ) ↑b := by
  constructor
  · norm_cast
    rw [Nat.le_floor_iff]
    · exact h.1
    · linarith [h.1]
  · norm_cast
    apply Nat.floor_le_of_le
    exact h.2

theorem floor_monotone_on {f : ℝ → ℝ} {m n : ℕ}
    (h : MonotoneOn f (Icc m n)) :
    MonotoneOn (fun x : ℝ ↦ f (Nat.floor x)) (Icc m n) := by
  intro x hx y hy hxy
  simp
  apply h
  · exact floor_Icc hx
  · exact floor_Icc hy
  · norm_cast
    exact Nat.floor_mono hxy

theorem ceil_Icc {a b : ℕ} {x : ℝ} (h : x ∈ Icc ↑a ↑b) :
    ↑(Nat.ceil x) ∈ Icc (↑a : ℝ) ↑b := by
  constructor
  · exact h.1.trans (Nat.le_ceil x)
  · norm_cast
    rw [Nat.ceil_le]
    exact h.2

theorem ceil_monotone_on {f : ℝ → ℝ} {m n : ℕ}
    (h : MonotoneOn f (Icc m n)) :
    MonotoneOn (fun x : ℝ ↦ f (Nat.ceil x)) (Icc m n) := by
  intro x hx y hy hxy
  simp
  apply h
  · exact ceil_Icc hx
  · exact ceil_Icc hy
  · norm_cast
    rw [Nat.ceil_le]
    exact hxy.trans (Nat.le_ceil y)

theorem monotone_integral_sum_upper_bound
    {f : ℝ → ℝ} {m n : ℕ} (hmn : m ≤ n) (h_monotone : MonotoneOn f (Set.Icc m n)) :
    ∫ x in m..n, f x ≥ ∑ k ∈ Finset.Ico m n, f k := by
  have hmn' : m ≤ n := hmn
  rify at hmn
  have hint : IntervalIntegrable f volume m n := by
    exact (Set.uIcc_of_le hmn ▸ h_monotone).intervalIntegrable
  have hint_floor : IntervalIntegrable (fun k ↦ f (Nat.floor k)) volume m n := by
    exact (Set.uIcc_of_le hmn ▸ floor_monotone_on h_monotone).intervalIntegrable
  exact calc
    ∫ x in m..n, f x
      ≥ ∫ x in m..n, f (Nat.floor x) := by
      simp
      refine intervalIntegral.integral_mono_on hmn hint_floor hint (fun x hx => ?_)
      exact h_monotone (floor_Icc hx) hx (Nat.floor_le (by linarith [hx.1]))
    _ = ∑ k ∈ Finset.Ico m n, ∫ x in k..k+1, f (Nat.floor x) := by
      have := intervalIntegral.sum_integral_adjacent_intervals_Ico
                (a := fun k => k) hmn' (fun k hk => hint_floor.mono_set ?_)
      · simp at this
        exact this.symm
      · simp
        rw [Set.uIcc_of_le hmn]
        apply Set.Icc_subset_Icc
        · aesop
        · norm_cast
          linarith [hk.2]
    _ = ∑ k ∈ Finset.Ico m n, f k := by
      have {k : ℕ} : ∫ x in k..k+1, f (Nat.floor x) = ∫ x in k..k+1, f k := by
        refine integral_congr_Ico (by simp) (fun x hx => ?_)
        congr
        exact Nat.floor_eq_on_Ico k x hx
      simp [this, intervalIntegral.integral_const]

theorem monotone_integral_sum_lower_bound
    {f : ℝ → ℝ} {m n : ℕ} (hmn : m ≤ n) (h_monotone : MonotoneOn f (Icc m n)) :
    ∫ x in m..n, f x ≤ ∑ k ∈ Finset.Ioc m n, f k := by
  have hmn' : m ≤ n := hmn
  rify at hmn
  have hint : IntervalIntegrable f volume m n := by
    exact (uIcc_of_le hmn ▸ h_monotone).intervalIntegrable
  have hint_ceil : IntervalIntegrable (fun k ↦ f (Nat.ceil k)) volume m n := by
    exact (uIcc_of_le hmn ▸ ceil_monotone_on h_monotone).intervalIntegrable
  exact calc
    ∫ x in m..n, f x
      ≤ ∫ x in m..n, f (Nat.ceil x) := by
      exact intervalIntegral.integral_mono_on hmn hint hint_ceil
        (fun x hx => h_monotone hx (ceil_Icc hx) (Nat.le_ceil x))
    _ = ∑ k ∈ Finset.Ico m n, ∫ x in k..k+1, f (Nat.ceil x) := by
      have := intervalIntegral.sum_integral_adjacent_intervals_Ico
                (a := fun k => k) hmn' (fun k hk => hint_ceil.mono_set ?_)
      · simp at this
        exact this.symm
      · simp
        rw [uIcc_of_le hmn]
        apply Icc_subset_Icc
        · aesop
        · norm_cast
          linarith [hk.2]
    _ = ∑ k ∈ Finset.Ioc m n, f k := by
      have {k : ℕ} : ∫ x in k..k+1, f (Nat.ceil x) = ∫ x in k..k+1, f (k + 1) := by
        refine integral_congr_Ioc (by simp) (fun x hx => ?_)
        congr
        norm_cast
        simp [Nat.ceil_eq_iff]
        aesop
      simp [this, ← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
      ring_nf

/- Theorem 1 -/
theorem integral_bound_monotone
    {f : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n) (h_monotone : MonotoneOn f (Icc (1 : ℕ) n)) :
    f 1 + ∫ x in 1..n, f x ≤ ∑ k ∈ Finset.Icc 1 n, f k ∧
  ∑ k ∈ Finset.Icc 1 n, f k ≤ f n + ∫ x in 1..n, f x := by
  constructor
  · calc
      f 1 + ∫ x in 1..n, f x
        ≤ f 1 + ∑ k ∈ Finset.Ioc 1 n, f k := by
          have := monotone_integral_sum_lower_bound hn h_monotone
          simp at this
          linarith [this]
      _ = ∑ k ∈ Finset.Icc 1 n, f k := by rw [Finset.Icc_eq_cons_Ioc hn, Finset.sum_cons]; simp
  · calc
      ∑ k ∈ Finset.Icc 1 n, f k
        = ∑ k ∈ Finset.Ico 1 n, f k + f n := (Finset.sum_Ico_add_eq_sum_Icc hn).symm
      _ ≤ f n + ∫ x in 1..n, f x := by
          have := monotone_integral_sum_upper_bound hn h_monotone
          simp at this
          linarith [this]

/- Theorem 2 -/
theorem integral_bound_antitone
    {f : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n) (h_antitone : AntitoneOn f (Icc 1 n)) :
    f n + ∫ x in 1..n, f x ≤ ∑ k ∈ Finset.Icc 1 n, f k ∧
    ∑ k ∈ Finset.Icc 1 n, f k ≤ f 1 + ∫ x in 1..n, f x := by
  have := integral_bound_monotone hn (by simpa using h_antitone.neg)
  exact ⟨by simpa [add_comm] using this.2, by simpa [add_comm] using this.1⟩

/- TODO: Theorem 3 -/
