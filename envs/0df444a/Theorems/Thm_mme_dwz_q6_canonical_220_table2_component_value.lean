-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_220_table2_component_value
-- name    : mme_dwz_q6_canonical_220_table2_component_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:20:08.527276+00:00
-- url     : https://prove2.me/theorems/f9d82f38-4cc8-47fb-9815-525d6ed6048b
-- title:
--   Exact Table-2 tau-value of the canonical $220$ block
-- statement:
--   Let $K$ be a field and let $\tau$ be real. The literal canonical $(2,2,0)$ block of the $q=6$ Coppersmith--Winograd square has tau-value at least its exact Table-2 component base
--
--   $$
--   38^{\tau}.
--   $$
--
--   The conclusion is stated on the canonical graded source block itself. It is obtained through the explicit restriction from $\langle1,38,1\rangle$ and the exact matrix-tensor power value, so it preserves the source constituent rather than asserting only a matching scalar dimension.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Lemma 4.6(b), Section 6.3 and Table 2, shape (2,2,0), PDF pp. 32-33 and 59-60; https://arxiv.org/abs/2210.10173.

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_CW_square_canonical_central220_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_MMObj_one_middle_one_tau_value

open MME MME.DWZSquare

set_option autoImplicit false

universe u

theorem mme_dwz_q6_canonical_220_table2_component_value
    {K : Type u} [Field K] (tau : ℝ) :
    HasTauValueAtLeast
      ((cwSquareCanonicalGrading K 6).blockSubtensor
        (cwSquareBlockType 2 2 0))
      tau (componentBase tau (11 : Fin 15)) := by sorry
