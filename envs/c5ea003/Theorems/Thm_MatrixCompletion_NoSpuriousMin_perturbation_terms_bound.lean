-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_perturbation_terms_bound
-- name    : MatrixCompletion.NoSpuriousMin.perturbation_terms_bound
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-08-04T14:12:35.640931+00:00
-- url     : https://prove2.me/theorems/c21e6513-94ab-4c7b-980d-7dde5be7a71c
-- title:
--   Uniform bound on the sampling and regularizer terms of $K$ (Chen–Li Lemma 4.8, exact case)
-- statement:
--   In the setting of the goal theorem — incoherent $Z$, tuning windows $\alpha\in[100,200]\cdot\sqrt{\nu_r}$ (where $\nu_r=\|ZZ^\top\|_{\ell_\infty}$, so $\sqrt{\nu_r}=\|Z\|_{2\to\infty}$) and $\lambda\in[100,200]\cdot\|\Omega-pJ\|$, sampling rate in the regime of Corollary 2.2, and a good sample $\Omega$ — the sampling-deviation and regularizer parts of the decomposition of $K$ are uniformly small along every aligned direction $\Delta=X-U$:
--
--   $$D_{\Omega,p}(\Delta\Delta^\top,\Delta\Delta^\top)-3D_{\Omega,p}(XX^\top-UU^\top,XX^\top-UU^\top)+\lambda\Bigl(\langle\Delta,\nabla^2R(X)[\Delta]\rangle-4\langle\nabla R(X),\Delta\rangle\Bigr)$$
--
--   $$\le\ \frac{p}{1000}\Bigl(\|\Delta^\top\Delta\|_F^2+\|U\Delta^\top\|_F^2\Bigr).$$
--
--   This is where the regularizer earns its keep: rows of $X$ larger than $\alpha$ are penalized strongly enough that the deviation terms they create are absorbed, while small rows are handled by the deterministic master bound with the spectral and tangent-space good-sample fields. This is the only milestone whose proof consumes the good-sample hypotheses.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion: Local Minima Analysis and Applications in Memory-efficient Kernel PCA, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3) [THE canonical reference: all milestones follow its Section 4], p. 19, Lemma 4.8, eq. (4.7), specialized to exact rank r (residual N = 0; bracket terms vanish under the sampling condition of Corollary 2.2). Consumes the good-sample facts (Chen-Li Lemmas 4.1-4.2) through Lemma 4.4.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.LinearAlgebra.Matrix.PosDef
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.perturbation_terms_bound
    {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hgood : GoodSample Z Ω p)
    (hU : U * Uᵀ = Z * Zᵀ) (hpsd : (Xᵀ * U).PosSemidef) :
    sampDev Ω p ((X - U) * (X - U)ᵀ) ((X - U) * (X - U)ᵀ)
        - 3 * sampDev Ω p (X * Xᵀ - U * Uᵀ) (X * Xᵀ - U * Uᵀ)
        + lam * (regHessQF α X (X - U) - 4 * innerM (regGrad α X) (X - U)) ≤
      p / 1000 * (frobSq ((X - U)ᵀ * (X - U)) + frobSq (U * (X - U)ᵀ)) := by sorry
