-- Prove2me | Theorems.Thm_mme_dwz_q6_112_table2_component_value_below
-- name    : mme_dwz_q6_112_table2_component_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T12:07:43.932345+00:00
-- url     : https://prove2.me/theorems/214dcb66-50fd-45eb-adfc-a7bcfd2a2e21
-- title:
--   Exact Table-2 b-split symmetric value for the coupled 112 component
-- statement:
--   For q=6, use the exact Duan--Wu--Zhou Section 6.3/Table 2 restricted split b=0.00021015 for the (1,1,2) coupled constituent. For every tau in the standard range 2 <= 3 tau and every nonnegative V strictly below
--
--   $$
--   \left(\frac{4}{(1-2b)^{1-2b}b^{2b}}\right)^{1/3}6^{(2-2b)\tau},
--   $$
--
--   the cyclic symmetrization of the coupled q=6 tensor has tau-value at least V^3; equivalently, the coupled tensor has symmetric tau-value at least V. The proof must use the exact finite Table-2 profile and may absorb only explicit subexponential losses; it must not assume endpoint attainment or an untwisted tensor realization.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 and Table 2 (b=0.00021015), plus Appendix A, proof of Lemma 4.6(d), PDF pp. 59-60 and 82-83; https://arxiv.org/abs/2210.10173.

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_q6_112_table2_primary_hash_family_rate
import Theorems.Thm_mme_dwz_q6_112_primary_hash_family_cyclic_value
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss

open Filter Topology
open MME MME.DWZSquare

set_option autoImplicit false

universe u

theorem mme_dwz_q6_112_table2_component_value_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < componentBase tau (12 : Fin 15)) :
    HasSymmetricTauValueAtLeast (coupledObj K 6) tau V := by
  sorry
