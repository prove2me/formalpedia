-- Prove2me | Theorems.Thm_mme_more_asymmetry_all_six_global_entropy_upper
-- name    : mme_more_asymmetry_all_six_global_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:00:37.191157+00:00
-- url     : https://prove2.me/theorems/0dc0635f-092e-4a35-b77b-2a363044727e
-- title:
--   Certified maximum-entropy bounds for all six rational More Asymmetry global regions
-- statement:
--   Let $D=\{(i,j,k)\in\{0,\ldots,8\}^3:i+j+k=8\}$ and let $\alpha_r$ be the explicit rational global-stage distributions of the published More Asymmetry witness data, in region order $XYZ,XZY,YXZ,YZX,ZXY,ZYX$. For every region $r$ and every probability distribution $\rho$ on $D$ with the same three coordinate marginals as $\alpha_r$,
--
--   $$H(\rho)=-\sum_{a\in D}\rho(a)\log\rho(a)\le U_r,$$
--
--   where the exact natural-logarithm entropy bounds are
--
--   $$ (U_1,\ldots,U_6)=\left(\frac{141510010583}{50000000000},\frac{70754987481}{25000000000},\frac{283020152309}{100000000000},\frac{283020257827}{100000000000},\frac{141509956499}{50000000000},\frac{7075506319}{2500000000}\right). $$
--
--   The convention is $0\log0=0$. The bounds hold for every competitor with the given marginals, with no assumed numerical logarithm estimates, optimizer optimality equations, or exact-marginal conditions on the auxiliary positive reference distributions. They certify all six global-stage maximum-entropy terms of this rationalized candidate. The recursive penalties, other rate terms, and tensor extraction remain separate obligations.
-- source:
--   Exact rational global-stage certificate for all six regions of the pinned released fourth-power witness. Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Proposition5.1/Theorem5.3 pp18–20 and numerical Section7; release https://osf.io/mw5ak/, code_matrix_mult.zip / data/W1.00_2.371339.mat. Explicit rational constants are definition3d3ddbe2-e2f6-468b-b59f-3f3c394d11c3. This certifies the derived rational data, not the raw floating-point optimizer vector. Direct proof dependencies are independent-positive-reference entropy certificate ae0df7ed-d414-4940-996c-8707d2ab69b7 and exact rational logarithm soundness f79fd5f9-9d45-427a-a128-f81b83b98053.

import Definitions.Def_mme_more_asymmetry_rational_global_entropy_data

open MME.MoreAsymmetryGlobalWitness BigOperators

set_option autoImplicit false

theorem mme_more_asymmetry_all_six_global_entropy_upper (r : Fin 6) (rho : Fin 45 → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 9),
      mme_modern_marginal (fun a ↦ coarseAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ coarseAddress a mode)
        (fun a ↦ (alpha r a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ (entropyUpper r : ℝ) := by sorry
