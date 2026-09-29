-- Prove2me | Theorems.Thm_VectorSpaceOpt_estimate_of_linear_function
-- name    : VectorSpaceOpt.estimate_of_linear_function
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T22:28:34.649319+00:00
-- url     : https://prove2.me/theorems/1236919f-b5d5-4fdb-84de-1282f1a61443
-- title:
--   The best estimate of a linear function of the parameters
-- statement:
--   Let $y$ and $\beta$ be random vectors with $E[yy^\top]$ invertible, and let $\hat\beta = E[\beta y^\top]\,(E[yy^\top])^{-1} y$ be the minimum-variance linear estimate of $\beta$. Then for an arbitrary $p \times n$ matrix $T$, the minimum-variance linear estimate of the linear function $T\beta$ is the same linear function of the estimate:
--
--   $$\widehat{T\beta} = T\,\hat\beta .$$
--
--   That is, among all linear estimates $\Gamma y$ of $T\beta$, the matrix $\Gamma = T \, E[\beta y^\top](E[yy^\top])^{-1}$ minimizes the error second moment in every component.
--
--   Estimation therefore commutes with linear maps: one need not re-solve the estimation problem for each functional of interest. The result follows from the componentwise optimality of the minimum-variance estimate, or directly from the projection theorem — the normal equations for the rows of $\Gamma$ are those of $\hat\beta$ premultiplied by $T$.
--
--   **Formalization Note.** Optimality is stated componentwise against every $p \times m$ matrix $\Gamma$; the second-moment matrices are uncentered, with explicit integrability hypotheses.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.6, Theorem 1, p. 91

import Mathlib
open Matrix MeasureTheory

namespace VectorSpaceOpt

theorem estimate_of_linear_function {m n p : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Ω → Fin m → ℝ) (β : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hβy : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => β ω i * y ω j) μ)
    (hββ : ∀ i j : Fin n, Integrable (fun ω => β ω i * β ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sβy : Matrix (Fin n) (Fin m) ℝ) (hSβy : ∀ i j, ∫ ω, β ω i * y ω j ∂μ = Sβy i j)
    (hdet : IsUnit Syy.det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = Sβy * Syy⁻¹)
    (T : Matrix (Fin p) (Fin n) ℝ) (Γ : Matrix (Fin p) (Fin m) ℝ) :
    ∀ i, ∫ ω, ((T * K₀).mulVec (y ω) i - T.mulVec (β ω) i) ^ 2 ∂μ ≤
         ∫ ω, (Γ.mulVec (y ω) i - T.mulVec (β ω) i) ^ 2 ∂μ := by sorry

end VectorSpaceOpt
