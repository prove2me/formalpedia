-- Prove2me | Theorems.Thm_mme_dwz_positive_116_original_profile_regional_restrict
-- name    : mme_dwz_positive_116_original_profile_regional_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T10:19:50.766968+00:00
-- url     : https://prove2.me/theorems/1670c8f8-63ee-4e77-abf7-f944a1ea00a8
-- title:
--   Original CW116 profile restricts to its exact three regional parent powers
-- statement:
--   Let $K$ be a field and let $q,m\geq0$ be integers. Write $T=T_{1,1,6}$ for the actual canonical constituent of the balanced fourth power of $\mathrm{CW}_q$, with its canonical Z basis and the literal grade of the left square. Let $p$ be the original integer Z profile of ledger object 149, and let $p^{(0)},p^{(1)},p^{(2)}$ and $A_0,A_1,A_2$ be the exact data in the published original-and-regional CW116 profile definition. The parent denominator is $10^{30}$; each regional denominator and the common weight denominator are $10^{15}$.
--
--   The following exact identities hold:
--   $$
--   \sum_{r=0}^{2}A_r=10^{15},\qquad
--   p_a=\sum_{r=0}^{2}p^{(r)}_aA_r
--   \quad(0\leq a\leq4),\qquad
--   10^{30}m=\sum_{r=0}^{2}10^{15}A_rm.
--   $$
--   Consequently there is a mode-wise linear tensor restriction
--   $$
--   T^{\otimes10^{30}m}[p]\longrightarrow
--   \bigotimes_{r=0}^{2}T^{\otimes10^{15}A_rm}[p^{(r)}].
--   $$
--   The prescribed-Z projections use the actual canonical constituent basis; all count and length equalities are exact integers. The original parent profile is unchanged. Although the numeric data originated in a $q=5$ certificate, this finite restriction holds for every $q$, including $q=6$.
--
--   This proves regional splitting of the parent before the recursive orientation and child-extraction steps. The target factors remain copies of the fourth-level parent, not square-child tensors. No typical-mixture mass, entropy estimate, lower-level decomposition, component value, or matrix-multiplication exponent bound is claimed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, Claim 7.1, https://arxiv.org/html/2210.10173v5#S7. Concrete original-profile instance from the supplied q=5 certificate, object149/address116, with exact regional profiles recorded in the public definition mme_dwz_positive_116_regional_profile_data. The restriction itself is uniform in q.

import Theorems.Thm_mme_dwz_prescribed_z_power_mixed_regional_restrict
import Definitions.Def_mme_dwz_positive_116_regional_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Mathlib.Tactic.FinCases

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent116
  Module BigOperators
open scoped Classical
universe u
set_option autoImplicit false

theorem mme_dwz_positive_116_original_profile_regional_restrict
    {K : Type u} [Field K] (q m : ℕ) :
    (∑ r, regionalWeight r = 1000000000000000) ∧
    (∀ a : Fin 5, parentProfile.count a =
      ∑ r, (regionalProfile r).count a * regionalWeight r) ∧
    parentProfile.length m =
      ∑ r, (regionalProfile r).length (regionalWeight r * m) ∧
    TensorObj.Restrict
      (TensorObj.kronFin 3 (fun r ↦ prescribedZPower
        (cwFourthConstituent K q 1 1 6)
        (constituentBasis K q 1 1 6 2)
        (fun a : LiftedCoarseCoordinate.{u} q 6 ↦ cwSquarePairGrade q a.down.val.1)
        (regionalProfile r) (regionalWeight r * m)))
      (prescribedZPower
        (cwFourthConstituent K q 1 1 6)
        (constituentBasis K q 1 1 6 2)
        (fun a : LiftedCoarseCoordinate.{u} q 6 ↦ cwSquarePairGrade q a.down.val.1)
        parentProfile m) := by sorry
