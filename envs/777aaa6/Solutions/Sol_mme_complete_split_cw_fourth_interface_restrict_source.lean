-- Prove2me | solution 1 for mme_complete_split_cw_fourth_interface_restrict_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:45:49.330276+00:00
-- url     : https://prove2.me/submissions/0a37f00f-9dc7-4cff-9a81-471044c56b29

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Theorems.Thm_mme_complete_split_interface_restrict_common_power

set_option autoImplicit false

universe u

open MME MME.StothersFourth MME.CompleteSplit MME.CompleteSplit.CWFourth
open scoped BigOperators NNReal
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {r : ℕ}
    (q : ℕ) (I J L : Fin r → Fin 9)
    (beta : Fin r → Fin 3 → Profile 3) (epsilon : ℝ≥0) (n : Fin r → ℕ) :
    TensorObj.Restrict
      (TensorObj.kronFin r
        (fun t ↦ restrictedConstituentPower K q (I t) (J t) (L t)
          (beta t) epsilon (n t)))
      ((cwFourthObj K q).kronPow (∑ t, n t)) := by
  exact mme_complete_split_interface_restrict_common_power
    (cwFourthObj K q)
    (fun t ↦ cwFourthConstituent K q (I t) (J t) (L t))
    (fun t ↦ constituentBasis K q (I t) (J t) (L t))
    (fun t ↦ constituentLabel q (I t) (J t) (L t))
    beta epsilon n
    (fun t ↦ ⟨fun i ↦ (cwFourthCanonicalGrading K q).blockProj i
      (cwFourthBlockType (I t) (J t) (L t) i), rfl⟩)

