-- Prove2me | Definitions.Def_Logic_DPCompletenessApplications
-- name    : Logic_DPCompletenessApplications
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:06.58592+00:00
-- url     : https://prove2.me/theorems/58313399-3870-4be8-b613-c1de4adfcd74
-- title:
--   Aether Catalog definitions — Logic_DPCompletenessApplications
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DPCompletenessApplications`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DPCompletenessApplications.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessWalks
/-
# Applications and specialisations of the DP completeness theorem

Building on `Logic.DPCompleteness` and `Logic.DPCompletenessWalks` this file records three
consequences of the general theory.

1. **Order duality (min-plus / shortest paths).**  Replacing the weight order by its dual turns
   the "greatest score" completeness theorem into a *minimality* theorem: every labelling
   *dominates* some dual DP run.  This is the Bellman–Ford shortest-path statement, obtained
   for free from the max-plus one.
2. **Closed form for stage-independent weights.**  When all transitions carry the same weight
   `c`, the value function collapses to `sup init + n • c`.
3. **A fully explicit three-state integer instance**, where the abstract value function is
   checked, inside Lean's kernel, against a brute-force enumeration of *all* labellings.
   This is a machine-checked instance of the completeness/exactness theorem.
-/


namespace Logic.DPCompleteness

namespace DPSpec

/-! ## Order duality: minimising runs -/

section Dual

variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
  [IsOrderedCancelAddMonoid W]

/-- The same DP data, read in the order-dual weight monoid.  Maximisation becomes
minimisation. -/
def dual (D : DPSpec S W) : DPSpec S Wᵒᵈ := ⟨D.init, D.step⟩





end Dual

/-! ## Stage-independent weights -/

section Const

variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]


end Const

/-! ## An explicit three-state integer instance -/

section Example

/-- The transition weight matrix of the running example. -/
def exA : Fin 3 → Fin 3 → ℤ
  | 0, 0 =>  2 | 0, 1 => -1 | 0, 2 =>  3
  | 1, 0 =>  1 | 1, 1 =>  0 | 1, 2 => -2
  | 2, 0 => -3 | 2, 1 =>  4 | 2, 2 =>  1

/-- A concrete stage-independent DP specification on three states with integer weights. -/
def exD : DPSpec (Fin 3) ℤ := ⟨fun s => (s : ℤ), fun _ s t => exA s t⟩

/-- All labellings of stages `0 … n`, as lists of length `n + 1`. -/
def exLabellings : ℕ → List (List (Fin 3))
  | 0 => (List.finRange 3).map (fun s => [s])
  | (n + 1) => (exLabellings n).flatMap (fun p => (List.finRange 3).map (fun s => p ++ [s]))

/-- Accumulate the score of a labelling presented as a list. -/
def exListScoreAux (k : ℕ) (prev : Fin 3) (acc : ℤ) : List (Fin 3) → ℤ
  | [] => acc
  | s :: r => exListScoreAux (k + 1) s (acc + exD.step k prev s) r

/-- The score of a labelling presented as a list. -/
def exListScore : List (Fin 3) → ℤ
  | [] => 0
  | s :: r => exListScoreAux 0 s (exD.init s) r

/-- Brute-force optimum over *all* labellings of stages `0 … n` ending in state `t`. -/
def exBrute (n : ℕ) (t : Fin 3) : ℤ :=
  ((exLabellings n).filter (fun p => p.getLast? = some t)).foldl
    (fun a p => max a (exListScore p)) (-1000)




end Example

end DPSpec

end Logic.DPCompleteness


