-- Prove2me | solution 1 for mme_complete_split_cw_fourth_restrict_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:45:05.635601+00:00
-- url     : https://prove2.me/submissions/02243a4d-77f1-496c-a3de-97997d6647e2

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Theorems.Thm_mme_complete_split_power_projection_certificate
import Theorems.Thm_mme_restrict_kronPow

set_option autoImplicit false

universe u

open MME MME.StothersFourth MME.CompleteSplit MME.CompleteSplit.CWFourth
open scoped NNReal
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q : ℕ) (I J L : Fin 9)
    (beta : Fin 3 → Profile 3) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Restrict (restrictedConstituentPower K q I J L beta epsilon N)
      ((cwFourthConstituent K q I J L).kronPow N) ∧
    TensorObj.Restrict (restrictedConstituentPower K q I J L beta epsilon N)
      ((cwFourthObj K q).kronPow N) := by
  have hprofile : TensorObj.Restrict
      (restrictedConstituentPower K q I J L beta epsilon N)
      ((cwFourthConstituent K q I J L).kronPow N) :=
    (mme_complete_split_power_projection_certificate
      (cwFourthConstituent K q I J L) (constituentBasis K q I J L)
      (constituentLabel q I J L) beta epsilon N).1
  have hcoarse : TensorObj.Restrict
      (cwFourthConstituent K q I J L) (cwFourthObj K q) :=
    ⟨fun i ↦ (cwFourthCanonicalGrading K q).blockProj i (cwFourthBlockType I J L i), rfl⟩
  exact ⟨hprofile, hprofile.trans (mme_restrict_kronPow hcoarse N)⟩

