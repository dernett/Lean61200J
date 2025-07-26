import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Sym.Sym2

/- Section 1. -/
section

variable (P Q : Prop)

example : (P → Q) ↔ (¬ Q → ¬ P) := by
  nth_rewrite 2 [imp_iff_not_or]
  rw [not_not, or_comm, ← imp_iff_not_or]

end
/- Section 2 -/
section

variable (A B C : Prop)

#help tactic by_cases

theorem Theorem1 : (A → B) ∨ (B → C) := by
  by_cases h : B
  · left
    intro; assumption
  · right
    intro; contradiction

/- Mutual friends/strangers -/

inductive Mutual
  | Friend
  | Stranger
deriving Repr, DecidableEq

abbrev V := Finset.Icc 1 6
abbrev E := Sym2 V
/-
  NOTE: We assign "don't care" to self-edges since they
  aren't actually in the graph
-/
abbrev Assignment := E → Mutual

@[simp]
theorem ne_friend_iff_eq_stranger {m : Mutual} : m ≠ Mutual.Friend ↔ m = Mutual.Stranger := by
  cases m <;> simp

@[simp]
theorem ne_stranger_iff_eq_friend {m : Mutual} : m ≠ Mutual.Stranger ↔  m = Mutual.Friend := by
  cases m <;> simp

@[simp]
theorem friend_or_stranger {m : Mutual} : (m = Mutual.Friend) ∨ (m = Mutual.Stranger) := by
  cases m <;> simp

/- Is there a triangle where `C` colors all edges color `c` -/
def HasTriangle (A : Assignment) (m : Mutual) : Prop :=
  ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    A s(a, b) = m ∧ A s(a, c) = m ∧ A s(b, c) = m

theorem Theorem2 (A : Assignment)
  : HasTriangle A Mutual.Friend ∨ HasTriangle A Mutual.Stranger := by
  let p : V := ⟨1, by decide⟩
  let others : Finset V := Finset.univ.erase p
  let friends : Finset V := { q ∈ others | A s(p, q) = Mutual.Friend }
  let strangers : Finset V := { q ∈ others | A s(p, q) = Mutual.Stranger }
  have h_others : others.card = 5 := by aesop
  have h_a_b : friends.card + strangers.card = 5 := by
    have h_disjoint : Disjoint friends strangers := by
      rw [Finset.disjoint_iff_ne]
      aesop
    have h_union : friends ∪ strangers = others := by aesop
    rw [← h_others, ← h_union]
    symm; exact Finset.card_union_of_disjoint h_disjoint
  by_cases h : friends.card ≥ 3
  · obtain ⟨t, t_sub, t_card_eq_3⟩ := Finset.exists_subset_card_eq h
    obtain ⟨q, r, s, _, _, _, hqrs⟩ := Finset.card_eq_three.mp t_card_eq_3
    simp only [hqrs, Finset.insert_subset_iff] at t_sub
    have : p ≠ q ∧ A s(p, q) = Mutual.Friend := by aesop
    have : p ≠ r ∧ A s(p, r) = Mutual.Friend := by aesop
    have : p ≠ s ∧ A s(p, s) = Mutual.Friend := by aesop
    by_cases h2 :
      A s(q, r) = Mutual.Friend ∨ A s(q, s) = Mutual.Friend ∨ A s(r, s) = Mutual.Friend
    · left
      obtain _ | _ | _ := h2
      · use p, q, r; repeat simp [*]
      · use p, q, s; repeat simp [*]
      · use p, r, s; repeat simp [*]
    · right
      use q, r, s; repeat simp [*] at *
  · push_neg at h
    have h_b_card : strangers.card ≥ 3 := by grind
    obtain ⟨t, t_sub, t_card_eq_3⟩ := Finset.exists_subset_card_eq h_b_card
    obtain ⟨q, r, s, _, _, _, hqrs⟩ := Finset.card_eq_three.mp t_card_eq_3
    simp only [hqrs, Finset.insert_subset_iff] at t_sub
    have : p ≠ q ∧ A s(p, q) = Mutual.Stranger := by aesop
    have : p ≠ r ∧ A s(p, r) = Mutual.Stranger := by aesop
    have : p ≠ s ∧ A s(p, s) = Mutual.Stranger := by aesop
    by_cases h2 :
      A s(q, r) = Mutual.Stranger ∨ A s(q, s) = Mutual.Stranger ∨ A s(r, s) = Mutual.Stranger
    · right
      obtain _ | _ | _ := h2
      · use p, q, r; repeat simp [*]
      · use p, q, s; repeat simp [*]
      · use p, r, s; repeat simp [*]
    · left
      use q, r, s; repeat simp [*] at *

end
/- Section 4 -/
section

theorem Theorem4 {P : ℕ → Prop} (hzero : P 0) (ih : ∀ n, ∀ m < n, P m → P n) : ∀ n, P n := by
  intro n
  induction n with
  | zero => assumption
  | succ n ih2 =>
    specialize ih (n + 1) n
    simp at ih
    exact ih ih2

/- Example 1: stacking blocks -/

def valid_split (split : ℕ → ℕ × ℕ) (n : ℕ) : Prop :=
  match split n with
  | (m₁, m₂) => m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₁ + m₂ = n

structure Strategy where
  split : ℕ → ℕ × ℕ
  next : ℕ → Strategy × Strategy -- TODO: this is a little sus?
  valid : ∀ n ≥ 2, valid_split split n

lemma split_lt {S : Strategy} {n m₁ m₂ : ℕ} (hn : n ≥ 2)
  (h_split : S.split n = (m₁, m₂)) : m₁ < n ∧ m₂ < n := by
  have := S.valid n hn
  unfold valid_split at this
  rw [h_split] at this
  simp at this
  grind

lemma split_eq {S : Strategy} {n m₁ m₂ : ℕ} (hn : n ≥ 2)
  (h_split : S.split n = (m₁, m₂)) : m₁ + m₂ = n := by
  have := S.valid n hn
  unfold valid_split at this
  rw [h_split] at this
  simp [*]

def F (n : ℕ) (S : Strategy) : ℕ :=
  if hn : n < 2 then
    0
  else
    match h_split : S.split n, h_next : S.next n with
    | (m₁, m₂), (S₁, S₂) => m₁ * m₂ + (F m₁ S₁) + (F m₂ S₂)
  termination_by n
  decreasing_by
  · push_neg at hn; exact (split_lt hn h_split).1
  · push_neg at hn; exact (split_lt hn h_split).2

theorem Theorem5 (n : ℕ) (S : Strategy) : F n S = (n * (n - 1) / 2 : ℚ) := by
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    unfold F
    by_cases hn : n < 2
    · match n with
      | 0 | 1 => simp
    · simp [if_neg hn]
      push_neg at hn
      match h_split : S.split n, h_next : S.next n with
      | (m₁, m₂), (S₁, S₂) =>
        have h_eq : m₁ + m₂ = n := split_eq hn h_split
        obtain ⟨h_lt₁, h_lt₂⟩ := split_lt hn h_split
        simp only [h_split, h_next] at *
        rw [ih m₁ h_lt₁, ih m₂ h_lt₂, ← h_eq]
        field_simp
        ring

end
