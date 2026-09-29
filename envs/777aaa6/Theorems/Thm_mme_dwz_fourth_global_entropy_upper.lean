-- Prove2me | Theorems.Thm_mme_dwz_fourth_global_entropy_upper
-- name    : mme_dwz_fourth_global_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T06:46:42.372147+00:00
-- url     : https://prove2.me/theorems/63664deb-855a-4e5a-9723-a0de29647ace
-- title:
--   Certified global maximum-entropy upper bound for the rational DWZ fourth-power candidate
-- statement:
--   Let $\alpha$ be the published exact rational global distribution of the DWZ fourth-power candidate, indexed by the 45 nonnegative triples $(i,j,k)$ with $i+j+k=8$. For every probability distribution $\rho$ on these same cells with the same X, Y, and Z marginals as $\alpha$, its natural-log entropy satisfies
--
--   $$H(\rho)\le \frac{2830114015881672025944380699373}{10^{30}}.$$
--
--   The rational right-hand side is the published `entropyUpper`; the inequality is uniform over all distributions in the marginal fiber, including boundary distributions. No claim that an optimizer is exact or that a numerical reference has the prescribed marginals is assumed. This closes the global maximum-entropy subproblem for this particular rational witness. It does not certify the remaining scalar rate terms, recursive component values, source-order conditions, tensor extraction, or omega<2.37193.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, global Equation (25), printed p.58. Candidate based on the authors' fourth-power data https://osf.io/dta6p/, power4_dup_2.371919.mat SHA256 2aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb. Exact data are definitionf99d9be9-2a29-4f1d-a088-6deb77a2e185. Entropy duality reuses mme_modern_entropyNat_upper_from_positive_reference (ae0df7ed), and the logarithms use mme_log_interval_of_exact_rational_series_certificate (f79fd5f9). This is a certificate for a deliberately rationalized distribution, not a claim that rounded MATLAB outputs are exact.

import Definitions.Def_mme_dwz_fourth_rational_global_entropy_data

open MME.DWZFourthGlobalWitness BigOperators
set_option autoImplicit false

theorem mme_dwz_fourth_global_entropy_upper (rho : Fin 45 → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 9),
      mme_modern_marginal (fun a ↦ coarseAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ coarseAddress a mode)
        (fun a ↦ (alpha a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ (entropyUpper : ℝ) := by sorry
