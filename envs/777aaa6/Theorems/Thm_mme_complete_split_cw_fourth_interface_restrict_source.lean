-- Prove2me | Theorems.Thm_mme_complete_split_cw_fourth_interface_restrict_source
-- name    : mme_complete_split_cw_fourth_interface_restrict_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:32:25.486708+00:00
-- url     : https://prove2.me/theorems/e09ed8b1-5549-4353-b4a1-2822d70224c6
-- title:
--   Canonical CW fourth complete-profile interfaces restrict from one common CW power
-- statement:
--   For every field and q, form a finite product of actual CW fourth coarse constituents, each raised to its own nonnegative integer power and restricted using its canonical four-letter mode labels and three complete-split profiles. This literal tensor product restricts from the (sum of the constituent powers)th power of the existing CW fourth tensor. No arbitrary tensor, basis, or label identification is left as a hypothesis. Empty products and zero powers follow the existing tensor-unit convention. This gives the finite ambient-source realization of a level-three interface tensor; it does not assert nonzero terms, disjoint copies, entropy rates, or asymptotic value.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definition 4.1 on printed p.15, with the complete-profile restrictions of Definitions 3.4-3.6. q=5 is the fourth-power source for the 2.37134 workstream. The finite projection holds for every coarse triple, including zero blocks; source-valid level-three constituent applications choose I+J+L=8 separately.

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Theorems.Thm_mme_complete_split_interface_restrict_common_power

set_option autoImplicit false

universe u

open MME MME.StothersFourth MME.CompleteSplit MME.CompleteSplit.CWFourth
open scoped BigOperators NNReal

theorem mme_complete_split_cw_fourth_interface_restrict_source
    {K : Type u} [Field K] {r : ℕ}
    (q : ℕ) (I J L : Fin r → Fin 9)
    (beta : Fin r → Fin 3 → Profile 3) (epsilon : ℝ≥0) (n : Fin r → ℕ) :
    TensorObj.Restrict
      (TensorObj.kronFin r
        (fun t ↦ restrictedConstituentPower K q (I t) (J t) (L t)
          (beta t) epsilon (n t)))
      ((cwFourthObj K q).kronPow (∑ t, n t)) := by sorry
