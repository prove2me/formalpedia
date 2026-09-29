-- Prove2me | Definitions.Def_Logic_StronglyCompleteSets_Contrarian
-- name    : Logic_StronglyCompleteSets_Contrarian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:08:06.234073+00:00
-- url     : https://prove2.me/theorems/ce9aeb31-4bcc-4d5a-8a31-b10703ccc861
-- title:
--   Aether Catalog definitions — Logic_StronglyCompleteSets_Contrarian
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.StronglyCompleteSets.Contrarian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/StronglyCompleteSets/Contrarian.lean by skeleton subtraction
import Mathlib

/-!
# Strongly complete sets: structural results and a counterexample

This file formalizes the basic notions from *Strongly complete sets and a conjecture
of Erdős*.  It then tests the tempting strengthening “every complete set is strongly
complete”.  The statement is false: the set consisting of all even natural numbers
together with `1` is complete, but deleting `1` leaves a parity obstruction.

We also prove that strong completeness is unchanged by a finite perturbation.  This
isolates the robustness built into the paper's definition.
-/

namespace StronglyCompleteSets

/-- `n` is a sum of distinct elements of `A`.  Distinctness is encoded by a finset. -/
def IsSubsetSum (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, (s : Set ℕ) ⊆ A ∧ ∑ a ∈ s, a = n

/-- Every sufficiently large natural number is a sum of distinct elements of `A`. -/
def Complete (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, IsSubsetSum A n

/-- Deleting an arbitrary finite set leaves a complete set. -/
def StronglyComplete (A : Set ℕ) : Prop :=
  ∀ F : Set ℕ, F.Finite → Complete (A \ F)





/-- A concrete complete set with one indispensable odd element. -/
def evenWithOne : Set ℕ := {n | Even n} ∪ {1}



end StronglyCompleteSets


