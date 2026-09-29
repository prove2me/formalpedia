-- Prove2me | Theorems.Thm_mme_cyclic_kron_two_strict_below_product
-- name    : mme_cyclic_kron_two_strict_below_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:29:40.822045+00:00
-- url     : https://prove2.me/theorems/043b5ea4-dce5-4c92-987c-6b0f2854dbde
-- title:
--   Strict cyclic tau-value product for two tensor factors
-- statement:
--   Let A and B be three-tensors over a field. If the cyclic symmetrization of A has every nonnegative tau-value strictly below a positive endpoint A0, and that of B has every nonnegative tau-value strictly below a positive endpoint B0, then the cyclic symmetrization of A tensor B has every nonnegative tau-value strictly below A0 B0. This is the two-factor strict product rule used to assemble the coupled and matrix-multiplication factors in the Phi233 constituents.
-- source:
--   Standard multiplicativity of asymptotic tensor value under tensor product, in the strict-below formulation used by the laser-method constituent analysis.

import Mathlib.Tactic
import Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_cyclic_kron_two_strict_below_product
    {K : Type u} [Field K]
    (A B : TensorObj K 3) (tau endpointA endpointB : ℝ)
    (hendpointA : 0 < endpointA) (hendpointB : 0 < endpointB)
    (hA : ∀ V : ℝ, 0 ≤ V → V < endpointA →
      HasTauValueAtLeast (cyclicSymmetrization A) tau V)
    (hB : ∀ V : ℝ, 0 ≤ V → V < endpointB →
      HasTauValueAtLeast (cyclicSymmetrization B) tau V)
    (V : ℝ) (hV : 0 ≤ V) (hVlt : V < endpointA * endpointB) :
    HasTauValueAtLeast
      (cyclicSymmetrization (TensorObj.kron A B)) tau V := by
  sorry
