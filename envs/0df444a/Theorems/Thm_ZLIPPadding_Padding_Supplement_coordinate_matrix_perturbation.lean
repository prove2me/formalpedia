-- Prove2me | Theorems.Thm_ZLIPPadding_Padding_Supplement_coordinate_matrix_perturbation
-- name    : ZLIPPadding.Padding.Supplement.coordinate_matrix_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:23:27.015262+00:00
-- url     : https://prove2.me/theorems/2904381a-0406-4179-bfb3-503dccde4a0b
-- title:
--   Lemma 4.7 — Perturbation after signed division
-- statement:
--   In the uniform-shell setting, let $x=Oa\in S_m(L)$ and let $\widehat C_x$ and $\widehat\kappa$ be estimates. Set $\widehat\beta=(m^2/n-\widehat\kappa)/(n+2)$, $\widehat D_x=(\widehat C_x-\widehat\beta K_x)/\widehat\kappa$, $e=|\widehat\kappa-\kappa|$ and $t=\|\widehat C_x-C_x\|_{\mathrm{op}}$. If $e<|\kappa|$, then
--
--   $$\|\widehat D_x-D_x\|_{\mathrm{op}}\le\frac{t+me}{|\kappa|-e}.$$
--
--   No hypothesis assumes that the coordinate label has already been recovered. The estimate controls the matrix before exact spectral rounding.
--
--   Differences from the source:
--   - generalization: the empirical matrix and signed scalar estimates defined in (4.14) and (4.17) → an arbitrary real matrix and real scalar estimate with the same strict error bound; reason: the deterministic operator-norm argument needs no further property of the estimates; substituting the source estimates gives its complete inequality
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed p. 20 (PDF p. 21), Lemma 4.7

import Definitions.Def_ZLIPPadding_Padding_Supplement_Statistics

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

theorem coordinate_matrix_perturbation (n m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m)
    (O : RMat n) (hO : Orthogonal O) (μ : PMF (ZVec n))
    (hμ : UniformOn μ (shell n m)) (a : ZVec n) (ha : a ∈ shell n m)
    (cHat : RMat n) (kh : ℝ) (he : |kh-shellKappa n m| < |shellKappa n m|) :
    opNorm (estimateD m (rotate O (liftZ a)) cHat kh-coordinateD O a) ≤
      (opNorm (cHat-momentC O m μ (rotate O (liftZ a))) +
        m*|kh-shellKappa n m|)/(|shellKappa n m|-|kh-shellKappa n m|) := by sorry

end ZLIPPadding.Padding.Supplement
