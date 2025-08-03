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
