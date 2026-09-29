-- Prove2me | Theorems.Thm_mme_complete_split_cw_fourth_restrict_source
-- name    : mme_complete_split_cw_fourth_restrict_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:27:25.586688+00:00
-- url     : https://prove2.me/theorems/1b219ecb-abfe-4d68-802a-8ff1cfdb3754
-- title:
--   Actual complete-profile CW fourth powers restrict the common CW source
-- statement:
--   The complete-profile restriction using the canonical bases and full four-letter labels of an actual (I,J,L) constituent is a literal restriction of that constituent's Nth power, and also of the Nth power of the existing literal fourth CW tensor. The proof uses the already proved generic complete-split projection, the actual canonical coarse block projection, restriction under tensor powers, and transitivity. This finite bridge supplies concrete source restrictions to common-interface product theorems; it is not an asymptotic extraction or lower-value theorem.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, printed pp.14-15, Definitions 3.4-3.6. Literal level-three full-word labels on the existing fourth-power CW tensor; q=5 is the More Asymmetry consumer.

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Theorems.Thm_mme_complete_split_power_projection_certificate
import Theorems.Thm_mme_restrict_kronPow

set_option autoImplicit false

universe u

open MME MME.StothersFourth MME.CompleteSplit MME.CompleteSplit.CWFourth
open scoped NNReal

theorem mme_complete_split_cw_fourth_restrict_source
    {K : Type u} [Field K] (q : ℕ) (I J L : Fin 9)
    (beta : Fin 3 → Profile 3) (epsilon : ℝ≥0) (N : ℕ) :
    TensorObj.Restrict (restrictedConstituentPower K q I J L beta epsilon N)
      ((cwFourthConstituent K q I J L).kronPow N) ∧
    TensorObj.Restrict (restrictedConstituentPower K q I J L beta epsilon N)
      ((cwFourthObj K q).kronPow N) := by sorry
