-- Prove2me | solution 1 for mme_regional_parent_partition_fine_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:43:49.737775+00:00
-- url     : https://prove2.me/submissions/8aa049bc-9da1-44f1-8766-c853ca7f73c7

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

/-- A partition of parent words induces a child-position order that agrees
with literal left/right splitting of the same fine word. -/
theorem solution
    {R T : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ Fin T) :
    ∃ childPositions : Fin (T * 2) ≃ Position n,
      ∀ (x : ProfiledCW.FineWord (T * 4)) (p : Position n),
        ProfiledCW.split childPositions (show (T * 2) * 2 ^ (2 - 1) = T * 4 by omega) x p =
          (let v := completeWordSplitEquiv 2 (by decide)
            (ProfiledCW.split (Equiv.refl (Fin T)) rfl x (positions ⟨p.1,p.2.1⟩))
          ![v.1,v.2] p.2.2) := by
  let e : Fin (T * 2) ≃ Position n := finProdFinEquiv.symm.trans
    ((positions.symm.prodCongr (Equiv.refl (Fin 2))).trans
      (Equiv.sigmaProdDistrib (fun r => Fin (n r)) (Fin 2)))
  refine ⟨e, ?_⟩
  rintro x ⟨r,t,h⟩
  funext j
  fin_cases h <;> fin_cases j <;>
    simp [ProfiledCW.split, e, completeWordSplitEquiv, fineWordSplitEquiv,
      Equiv.sigmaProdDistrib, finProdFinEquiv, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc]

#print axioms solution
