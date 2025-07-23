import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Basic

/- Section 3. Propositions -/
section

/- Examples: -/

#help tactic unfold
#help tactic decide

def Prop1 : Prop := 2 + 3 = 5
example : Prop1 := by unfold Prop1; decide

def Prop2 : Prop := 2 + 3 = 6
example : ¬ Prop2 := by unfold Prop2; decide

def Prop3 : Prop := ∀ n : ℕ, Nat.Prime (n ^ 2 + n + 41)

/- Non-examples: -/

/- These are `String`s, not `Prop`s. -/
#check ("Hello" : String)
#check ("Who are you?" : String)

/- This one gives an error! -/
/-
def self_reference : Prop := ¬ self_reference
-/

/- Prop3 -/
def Prop3_row (n : ℕ) : ℕ × ℕ × Bool :=
  ⟨n, n ^ 2 + n + 41, Nat.Prime (n ^ 2 + n + 41)⟩

/- LLM generated code -/
def Prop3_print_table : IO Unit := do
  -- Print the table header
  IO.println "┌─────┬────────────────┬───────────┐"
  IO.println "│   n │ p(n) = n²+n+41 │ Is Prime? │"
  IO.println "├─────┼────────────────┼───────────┤"

  -- Loop through natural numbers from 0 to 41 (42 is exclusive)
  for i in List.range 42 do
    -- Get the data for the current row
    let ⟨n, p, isPrime⟩ := Prop3_row i

    -- Format each part of the data to align the columns.
    -- The padding values have been corrected to match the border widths.
    let nStr := (toString n).leftpad 5 ' '
    let pStr := (toString p).leftpad 16 ' '
    let isPrimeStr := (" " ++ toString isPrime).rightpad 11 ' '

    -- Print the formatted row. The format string now directly concatenates
    -- the correctly padded strings with the pipe separators.
    IO.println s!"│{nStr}│{pStr}│{isPrimeStr}│"

  -- Print the table footer
  IO.println "└─────┴────────────────┴───────────┘"

#eval Prop3_print_table

def Prop4 : Prop := ¬ ∃ a b c d : ℕ+, a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4
theorem Prop4_false : ¬ Prop4 := by
  unfold Prop4
  push_neg
  use 95800, 217519, 414560, 422481
  decide

def Prop5 : Prop := ∃ a b c d : ℕ+, a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4
example : Prop5 := by unfold Prop5; by_contra h; apply Prop4_false; exact h

def Prop6 : Prop := ¬ ∃ x y z : ℕ+, 313 * (x^3 + y^3) = z ^ 3
example : ¬ Prop6 := sorry

def Prop7 : Prop := ∀ n > 2, Even n → ∃ p q, Prime p ∧ Prime q ∧ n = p + q
example : Prop7 := sorry

end
/- Section 4. Combining Propositions -/
section

variable (A B : Prop)

#check A ∧ B
#check A ∨ B
#check ¬ A

end
/- Section 5. Implication -/
section

variable (A B : Prop)

#check A → B

/- Contrapositive -/
example : A → B ↔ ¬ B → ¬ A := not_imp_not.symm

end

/- Section 6. Sets -/
section

variable (U : Type)
def A : Finset ℕ := {6, 1, 2, 0}
#check ℕ
#check ℤ
#check (∅ : Set U)

/- IDK how to properly deal with heterogenous sets -/
/-
def B : Finset (ℕ ⊕ Set ℕ) := {.inl 2, .inr {3, 4}, .inr ∅}
-/

#eval ({1, 2, 2, 3} : Finset ℕ) = {2, 3, 1}

#eval A.card
#eval 6 ∈ A

/- Errors out -/
/-
example : ({1, 2} : Finset ℕ) ∉ A := sorry
-/

#eval {1, 2} ⊆ A
#eval {0, 1, 2, 6} ⊆ A

/- set-builder notation -/
#check {n : ℕ | Prime n}

/- Doesn't work: Sets must have same type. -/
/-
example : A ∩ B = {2} := sorry
-/

/- Ordered tuples -/
def X := (6, 1, 2, 0)
def Y := (2, 1, 6, 0)

#eval X ≠ Y

end
/- Section 7. Axioms -/
section

/- Formalization of Euclidean Geometry. -/
/- https://github.com/loganrjmurphy/LeanEuclid/ -/

/- Some examples of axioms -/
axiom Point : Type
axiom Line : Type
opaque Point.onLine : Point → Line → Prop

/- Our system is inconsistent if we can prove `False`. -/
/-
theorem inconsistent : False := sorry
-/

/- Decidable propositions are those that can be proved or disproved. -/
#check Decidable
#check Decidable.isTrue (rfl : 1 + 1 = 2)
#check Decidable.isFalse (by decide : 2 + 2 ≠ 5)

end
