import Lean61200J.Lectures.Lecture_05
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter
open Topology

def H (n : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 n, (1 / i : ℚ)

variable {α β : Type*} [Preorder α] [NormedField β] in
def Tilde (f g : α → β) : Prop := Tendsto (fun x ↦ f x / g x) atTop (𝓝 1)

theorem H_approx_ln : Tilde (fun n ↦ (H n : ℝ)) (fun x ↦ Real.log x) := by
  have h_antitone (n : ℕ) (hn : 1 ≤ n) : AntitoneOn (fun x : ℝ => 1 / x) (Set.Icc 1 n)  := by
    intros x y hxy
    intros
    simp
    gcongr
    linarith [y.1]
  have h_left : ∀ᶠ (n : ℕ) in atTop, 1 / (n * Real.log n) + 1 ≤ H n / Real.log n := by
    rw [eventually_atTop]
    use 2
    intro n hn'
    have hn : n ≥ 1 := by linarith
    have : 0 < Real.log n := Real.log_pos (by norm_cast)
    exact calc
      1 / (n * Real.log n) + 1
        = (1 / n + Real.log n) / (Real.log n) := by field_simp; ring
      _ = (1 / n + ∫ x in 1..n, 1 / x) / (Real.log n) := by
        simp
        rw [integral_inv]
        · simp
        · aesop
      _ ≤ (∑ k ∈ Finset.Icc 1 n, (1 / k : ℝ)) / (Real.log n) := by
        bound [integral_bound_antitone hn (h_antitone n hn)]
      _ = H n / Real.log n := by simp [H]
  have h_right : ∀ᶠ (n : ℕ) in atTop, H n / Real.log n ≤ 1 + 1 / Real.log n := by
    rw [eventually_atTop]
    use 2
    intro n hn'
    have hn : n ≥ 1 := by linarith
    have : 0 < Real.log n := Real.log_pos (by norm_cast)
    exact calc
      H n / Real.log n
        = (∑ k ∈ Finset.Icc 1 n, (1 / k : ℝ)) / (Real.log n) := by simp [H]
      _ ≤ (1 + ∫ x in 1..n, 1 / x) / (Real.log n) := by
        bound [integral_bound_antitone hn (h_antitone n hn)]
      _ = 1 + 1 / Real.log n := by
        simp
        rw [integral_inv]
        · field_simp
          ring
        · aesop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ h_left h_right
  · conv => enter [3, 1]; rw [← add_zero 1, add_comm]
    apply Tendsto.add_const
    have : Tendsto (fun n : ℕ => n * Real.log n) atTop atTop := by
      apply Tendsto.atTop_mul_atTop₀
      · exact tendsto_natCast_atTop_atTop
      · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    apply tendsto_inv_atTop_zero.comp at this
    unfold Function.comp at this
    simp [*] at *
    exact this
  · conv => enter [3, 1]; rw [← add_zero 1]
    apply Tendsto.const_add
    have := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    apply tendsto_inv_atTop_zero.comp at this
    unfold Function.comp at this
    simp [*] at *

/- TODO: Move this into separate file -/

def PReal := { x : ℝ // 0 < x }
notation "ℝ+" => PReal

@[coe]
def PReal.val : ℝ+ → ℝ := Subtype.val

instance coePRealReal : Coe ℝ+ ℝ :=
  ⟨PReal.val⟩

@[simp]
theorem PReal.pos (x : ℝ+) : 0 < (x : ℝ) :=
  x.2

@[simp]
theorem PReal.ne_zero (x : ℝ+) : (x : ℝ) ≠ 0 :=
  x.2.ne'

@[simp]
theorem PReal.zero_le (x : ℝ+) : (0 : ℝ) ≤ x :=
  le_of_lt x.pos

def O (g : ℕ+ → ℝ+) : Set (ℕ+ → ℝ) :=
  { f : ℕ+ → ℝ | ∃ c : ℝ, ∀ᶠ x in atTop, |f x| ≤ c * g x }

theorem limit_O {f : ℕ+ → ℝ} {g : ℕ+ → ℝ+}
    (h_ex_lim : ∃ l : ℝ, Tendsto (fun x ↦ |f x| / g x) atTop (𝓝 l)) :
    f ∈ O g := by
  obtain ⟨l, h_lim⟩ := h_ex_lim
  use l + 1
  rw [Metric.tendsto_atTop] at h_lim
  specialize h_lim 1 (by simp)
  obtain ⟨M, hM⟩ := h_lim
  rw [eventually_atTop]
  refine ⟨M, fun x hx ↦ ?_⟩
  specialize hM x hx
  rw [Real.dist_eq, abs_sub_lt_iff] at hM
  replace hM : |f x| / g x < l + 1 := by linarith
  exact calc
    |f x|
      = |f x| / g x * g x := by field_simp
    _ ≤ (l + 1) * g x := by bound
