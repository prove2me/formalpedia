-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_K_superlevel_bound_corrected
-- name    : MatrixCompletion.NoSpuriousMin.K_superlevel_bound_corrected
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-14T18:52:39.63974+00:00
-- url     : https://prove2.me/theorems/c6ac94ce-a2fe-44b8-89f4-f2bda37b7c86
-- title:
--   K superlevel bound (Chen–Li eq. 4.14, exact rank, corrected constants)
-- statement:
--   **Chen–Li eq. (4.14), exact-rank case, with usable constants.**
--
--   Under the hypotheses of `perturbation_terms_bound_corrected` — in particular the sampling rate $p\ge10^{28}\mu^4\kappa^4r^2(1+\log d)/d$ — write $\Delta=X-U$, $a=\|\Delta^\top\Delta\|_F$ and $b=\|\Delta^\top U\|_F$. Then Chen–Li's auxiliary function
--
--   $$K(X)=\langle\Delta,\nabla^2f(X)[\Delta]\rangle-4\langle\nabla f(X),\Delta\rangle$$
--
--   obeys
--
--   $$\frac{K(X)}{p}\;\le\;-1.98\,a^2+6.02\,ab-6\,b^2 .$$
--
--   The right-hand quadratic form is negative definite ($6.02^2=36.24<47.52=4\cdot1.98\cdot6$), so $K(X)\ge0$ forces $a=b=0$, i.e. $X=U$ and $XX^\top=ZZ^\top$.
--
--   The derivation is Chen–Li's: expand $\|XX^\top-UU^\top\|_F^2=\|\Delta\Delta^\top\|_F^2+2\|\Delta U^\top\|_F^2+2\langle\Delta U^\top,U\Delta^\top\rangle+4\langle\Delta\Delta^\top,U\Delta^\top\rangle$ (eq. 4.9), use the trace identities (4.10)–(4.12) and the positive-semidefiniteness fact $\langle\Delta^\top\Delta,(U+\Delta)^\top U\rangle\ge0$ (eq. 4.13) furnished by the alignment, then apply the $K_2+K_3$ bound.
--
--   **Why the constants differ from the mission's `K_superlevel_bound`.** That statement carries byte-identical hypotheses to `perturbation_terms_bound`, so the same counterexample refutes it (theorem `e9fd3204-431c-4a43-b81e-ff28bfcf8319`, disproof `ac265185-c5b6-4443-867c-a3b32ea9049b`). Chen–Li's published coefficients $-1.999,\,6.001$ are exactly what a $10^{-3}$ accuracy in Lemma 4.8 buys: the $10^{-3}\|U\Delta^\top\|_F^2$ on the right of (4.7) is matched against the $0.001$ of slack in splitting $-6\langle\Delta^\top\Delta,U^\top U\rangle$ as $-0.001-5.999$. With the accuracy $c=1/50$ that the mission's `tangent_conc` field actually supports, the same split gives $-(2-c)a^2+(6+c)ab-6b^2$; the form stays negative definite for every $c<0.33$, and $c=0.02$ yields the coefficients above.
-- source:
--   Chen, Li 2019, https://arxiv.org/abs/1711.01742 (v3), p. 20, eq. (4.14), via eqs. (4.8)-(4.13), exact-rank specialization, with the accuracy of Lemma 4.8 relaxed from 10^-3 to 1/50 and the sampling constant raised from 10^10 to 10^28.  The published coefficients -1.999/6.001 correspond to accuracy 10^-3; -1.98/6.02 correspond to 1/50.  The 10^10/10^-3 instantiation is refuted by submission ac265185-c5b6-4443-867c-a3b32ea9049b against theorem e9fd3204-431c-4a43-b81e-ff28bfcf8319.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.K_superlevel_bound_corrected
    {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hpC : 10 ^ 28 * μ ^ 4 * κ ^ 4 * (r : ℝ) ^ 2 * (1 + Real.log d) / d ≤ p)
    (hgood : GoodSample Z Ω p)
    (hU : U * Uᵀ = Z * Zᵀ) (hpsd : (Xᵀ * U).PosSemidef) :
    Kfun Z Ω lam α X U ≤
      p * (-(198 / 100) * frobSq ((X - U)ᵀ * (X - U))
        + (602 / 100) * frobNorm ((X - U)ᵀ * (X - U)) * frobNorm ((X - U)ᵀ * U)
        - 6 * frobSq ((X - U)ᵀ * U)) := by sorry
