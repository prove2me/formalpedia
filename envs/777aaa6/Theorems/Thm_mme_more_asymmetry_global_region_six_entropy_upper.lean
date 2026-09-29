-- Prove2me | Theorems.Thm_mme_more_asymmetry_global_region_six_entropy_upper
-- name    : mme_more_asymmetry_global_region_six_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:50:32.618839+00:00
-- url     : https://prove2.me/theorems/4f07a5d5-1643-4249-9f0c-5c99e4f336f7
-- title:
--   Certified maximum-entropy upper bound for rational More Asymmetry global region six
-- statement:
--   Let $D=\{(i,j,k)\in\{0,\ldots,8\}^3:i+j+k=8\}$, ordered first by $i$ and then by $j$, and let $\alpha_6$ be the sixth explicit rational global-stage distribution in the published More Asymmetry witness data. For every probability distribution $\rho$ on $D$ whose three coordinate marginals equal those of $\alpha_6$, its natural-logarithm entropy satisfies
--
--   $$H(\rho)=-\sum_{a\in D}\rho(a)\log\rho(a)\le\frac{7075506319}{2500000000}.$$
--
--   The convention is $0\log0=0$. This is a concrete upper bound over all distributions with the specified marginals, not an assumed optimizer value. It supplies one global-stage maximum-entropy penalty certificate for the rationalized fourth-power witness. It does not assert the whole numerical surplus or any tensor extraction.
-- source:
--   Exact-rational certificate for region6 (ZYX order) of the released More Asymmetry fourth-power witness. Alman et al., https://arxiv.org/abs/2404.16349v2, Proposition5.1 and Theorem5.3 pp18–20, Section7 numerical bound; code release https://osf.io/mw5ak/, code_matrix_mult.zip / data/W1.00_2.371339.mat. Exact rational data are Prove2Me3d3ddbe2-e2f6-468b-b59f-3f3c394d11c3. This is a new finite certificate for the rationalized candidate, not a claim that the raw floating-point optimizer vector is exactly feasible. Reuses independent-reference entropy upper theorem ae0df7ed-d414-4940-996c-8707d2ab69b7 and exact rational logarithm soundness f79fd5f9-9d45-427a-a128-f81b83b98053.

import Definitions.Def_mme_more_asymmetry_rational_global_entropy_data

open MME.MoreAsymmetryGlobalWitness BigOperators

set_option autoImplicit false

theorem mme_more_asymmetry_global_region_six_entropy_upper (rho : Fin 45 → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 9),
      mme_modern_marginal (fun a ↦ coarseAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ coarseAddress a mode)
        (fun a ↦ (alpha 5 a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ (entropyUpper 5 : ℝ) := by sorry
