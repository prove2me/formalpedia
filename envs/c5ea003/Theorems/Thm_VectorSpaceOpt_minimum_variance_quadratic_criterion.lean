-- Prove2me | Theorems.Thm_VectorSpaceOpt_minimum_variance_quadratic_criterion
-- name    : VectorSpaceOpt.minimum_variance_quadratic_criterion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T22:28:34.943211+00:00
-- url     : https://prove2.me/theorems/624ca814-a998-4b14-ac7c-2e42e26c6c43
-- title:
--   Optimality under any positive-semidefinite quadratic criterion
-- statement:
--   Let $\hat\beta = K_0 y$ with $K_0 = E[\beta y^\top](E[yy^\top])^{-1}$ be the linear minimum-variance estimate of $\beta$. Then $\hat\beta$ is also the linear estimate minimizing
--
--   $$E\big[(\beta - \hat\beta)^\top P (\beta - \hat\beta)\big]$$
--
--   for **every** positive-semidefinite $n \times n$ matrix $P$.
--
--   The minimum-variance estimate is thus not tied to the particular choice of the Euclidean error criterion: any weighting of the components, however unequal, and any correlated quadratic penalty is minimized by the same estimator. The proof takes $P^{1/2}$, the positive-semidefinite square root of $P$, and observes that $P^{1/2}\hat\beta$ is the minimum-variance estimate of $P^{1/2}\beta$ — the previous theorem applied to a linear function — so that $\hat\beta$ minimizes $E\|P^{1/2}(\beta - \hat\beta)\|^2$, which is the displayed criterion.
--
--   **Formalization Note.** The quadratic form is written as the explicit double sum $\sum_{i}\sum_{j} (\beta - Ky)_i P_{ij} (\beta - Ky)_j$; positive semidefiniteness is Mathlib's `Matrix.PosSemidef`, which includes symmetry.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.6, Theorem 2, p. 91

import Mathlib
open Matrix MeasureTheory

namespace VectorSpaceOpt

theorem minimum_variance_quadratic_criterion {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Ω → Fin m → ℝ) (β : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hβy : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => β ω i * y ω j) μ)
    (hββ : ∀ i j : Fin n, Integrable (fun ω => β ω i * β ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sβy : Matrix (Fin n) (Fin m) ℝ) (hSβy : ∀ i j, ∫ ω, β ω i * y ω j ∂μ = Sβy i j)
    (hdet : IsUnit Syy.det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = Sβy * Syy⁻¹)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (K : Matrix (Fin n) (Fin m) ℝ) :
    ∫ ω, (∑ i, ∑ j, (β ω i - K₀.mulVec (y ω) i) * P i j *
            (β ω j - K₀.mulVec (y ω) j)) ∂μ ≤
    ∫ ω, (∑ i, ∑ j, (β ω i - K.mulVec (y ω) i) * P i j *
            (β ω j - K.mulVec (y ω) j)) ∂μ := by sorry

end VectorSpaceOpt
