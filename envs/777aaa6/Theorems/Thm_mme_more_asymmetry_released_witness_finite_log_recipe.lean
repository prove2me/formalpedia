-- Prove2me | Theorems.Thm_mme_more_asymmetry_released_witness_finite_log_recipe
-- name    : mme_more_asymmetry_released_witness_finite_log_recipe
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-09-21T20:11:00.670976+00:00
-- url     : https://prove2.me/theorems/fc8f1ec2-0bc5-4655-9168-6515aad5a11d
-- title:
--   Realize the released stronger witness within explicit finite loss budgets
-- statement:
--   Construct a genuine finite logarithmic regional recipe for the q=5 Coppersmith–Winograd tensor, on 4n original copies, with n>0, positive input count and positive matrix volume. Its guaranteed logarithmic output count, after subtracting log(inputs), must be at least n(2.81302098456 - 0.000001). Its log matrix volume must be at least n(3*2.09612367517 - 0.0000001).
--
--   These fixed rational targets are motivated by a reconstruction of the released More Asymmetry numerical witness. The reconstruction normalizes 1,032 input distributions on the denominator 10^12, keeps 2,700 square-child parameters on the same grid, derives parent complete-split distributions by exact rational products and mixtures, and uses positive rational product-weight dual certificates to upper-bound same-marginal entropy maxima. Outward-rounded rational logarithm intervals give an asymptotic scalar surplus greater than 1.8e-6 at tau=3952233/5000000. That numerical computation is an external reproducible check, not a Lean proof of the whole witness or of an extraction.
--
--   The formal goal here is the missing finite realization: actual integer profiles and placements, source inclusions, exact unique type covers, recursive compatibility, boundary maps, and the stated explicit finite-loss budgets. The LogRecipe interface does not assume an extraction map or a copy-count conclusion. Its proved compiler supplies those from the checked budgets. The allowed total losses are 1e-6 for output/input rate and 1e-7 for log-volume per fourth-power block, leaving more than 8e-7 scalar surplus. It is not sufficient to restate the final exponent or postulate these count bounds without constructing a valid LogRecipe.
--
--   Exact seed SHA256: f8187420c24231b83d9d1fb7b327fee76cd50ada0af0525e77b3d3b0d8f4d4e6. Data support and denominator checks do not yet establish source compatibility or the type-cover conditions.
--
--   The full exact primitive input tables are publicly available as [mme_more_asymmetry_released_exact_profile_seed](https://prove2.me/theorems/cb80ec03-0b0a-4b6c-a75e-ca788b94d914). Their elementary normalization and consistency are [Lean-kernel proved](https://prove2.me/theorems/87a4b7d4-04ba-4e88-835b-c15dca0975c0). These data and checks can be reused in the construction; the full derived numerical entropy evaluation and physical realization still require formal connection.
-- source:
--   More Asymmetry, arXiv:2404.16349v2; W1.00_2.371339.mat SHA256 783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3

import Definitions.Def_mme_logarithmic_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_more_asymmetry_released_witness_finite_log_recipe :
    ∃ (n ell : ℕ) (P : Predicate (4 * n)) (D : LogRecipe (4 * n) ell P),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (n : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 1000000) +
          Real.log (D.inputs : ℝ) ≤ D.logOutputs ∧
      (n : ℝ) * (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 10000000) ≤
          Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by sorry
