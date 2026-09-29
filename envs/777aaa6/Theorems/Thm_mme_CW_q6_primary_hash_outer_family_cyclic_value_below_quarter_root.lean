-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_outer_family_cyclic_value_below_quarter_root
-- name    : mme_CW_q6_primary_hash_outer_family_cyclic_value_below_quarter_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:59:48.616807+00:00
-- url     : https://prove2.me/theorems/9429e0be-59bd-4d58-ad93-0aefd8104a41
-- title:
--   Source-faithful q=6 outer C-tensor family attains every strict finite rate
-- statement:
--   Fix the coupled q=6 constituent and tau with 3 tau at least 2. For every sufficiently large primary profile N satisfying the standard Coppersmith--Winograd floor conditions, let the retained induced hash family consist of A outer C-tensor fibers with common inner size H and component volume 6^(4G+2L). Then every nonnegative W strictly below
--
--   $$(R(\tau)e^{-\ell_N/2})^{2N}, \qquad R(\tau)=4\,6^{3\tau}(6^{3\tau}+2),$$
--
--   is attained by the tau-value of the cyclic symmetrization of the 2N-th tensor power.
--
--   The proof keeps the source-faithful heterogeneous C-tensor family: the first hashing estimates imply the lower bound A^3 H^2, the common component volume supplies the remaining tau-weight, and the outer-family C-tensor theorem performs the second balancing. No fixed common survivor tensor is assumed.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), primary hashing and C-tensor value argument on journal pp. 270--272; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value

open MME Filter Topology

universe u

theorem mme_CW_q6_primary_hash_outer_family_cyclic_value_below_quarter_root
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∀ W : ℝ, 0 ≤ W →
        W < (raw * Real.exp (-(loss / 2))) ^ (2 * N) →
        HasTauValueAtLeast
          (cyclicSymmetrization ((coupledObj K 6).kronPow (2 * N)))
          tau W := by
  sorry
