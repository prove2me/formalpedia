-- Prove2me | Theorems.Thm_rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense
-- name    : rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T04:21:59.274689+00:00
-- url     : https://prove2.me/theorems/41cccb0d-747a-4021-a49a-a4c3223d9596
-- statement:
--   Rudelson 1999 (JFA 164) Thm 1 Steps 1-2 (symmetrization + matrix non-commutative Khintchine on rank-one tensors), packaged as the expected-operator-norm vs sqrt(sampled-Gram operator norm) moment engine: there is an absolute Csym>0 such that under the coordinate radius bound ||P_T(e_i e_j*)||_F <= R, the expected centered vectorized operator norm E_Omega[ p^{-1} || sum_ab (delta_ab - p) y_ab tensor y_ab ||_op ] is bounded by Csym * (sqrt(log(max n1 n2)/p) * R) * E_Omega[ sqrt(p^{-1} || sum_{ab in Omega} y_ab tensor y_ab ||_op) ]. The outer expectation is kept a first moment; the sqrt(log/p) gain is the Khintchine sqrt(2q) at q approx log d with the window d^{1/2q} <= e. Step 1 = Ledoux-Talagrand symmetrization (Bernoulli centering to Rademacher sign); Step 2 = matrix Rademacher 2p-moment / Lust-Picquard-Pisier Khintchine with Loewner variance proxy normV = max||y||^2 * ||sum_Omega y tensor y|| <= R^2 ||G_Omega||.
-- source:
--   Rudelson 1999 JFA 164 Thm 1 Steps 1-2; Candes-Recht 2009 arXiv:0805.4471 section 9.1; Pisier section 3 / Lust-Picquard noncommutative Khintchine; Ledoux-Talagrand Lemma 6.3.

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

/-
CARVE B — Rudelson 1999 (JFA 164) Thm 1 Steps 1+2 (symmetrization + matrix
non-commutative Khintchine on the rank-one tensors), packaged as the
EXPECTED-operator-norm vs `√(sampled-Gram operator norm)` moment engine.

This is the genuine Mathlib-absent operator-space content of the route:
  Step 1 (Ledoux–Talagrand Lemma 6.3 / W3 7ade53da): Bernoulli centering
    `(δ-p)` → Rademacher-signed `ε·δ`, lifting the outer expectation to a
    sign-average while keeping it a first moment.
  Step 2 (Pisier §3 / Lust-Picquard; matrix Rademacher 2p-moment engine
    b6bf4feb/0cafa5a3 at q≈log d, window collapse `d^{1/2q}≤e` c559deb6,
    reindex e66e5c47, Loewner variance-proxy d24a0b1f, collapse
    `(yy*)²=‖y‖²yy*` f76d68af): the matrix Khintchine bound, with the
    variance proxy `normV = max‖y‖²·‖∑δ y⊗y‖ ≤ R²·‖G_Ω‖` (coordinate radius
    bound `‖y_ab‖²≤R²`).

The clean engine output keeps the SAMPLED-Gram operator norm `‖G_Ω‖`
(uncentered) under a per-Ω square root, fed afterwards by the eq(2.1)
self-bound `‖G_Ω‖ ≤ p(Z_Ω+1)` (carve A) and the outer concave √-Jensen.

`G_Ω = ∑_{ab∈Ω} y_ab ⊗ y_ab`,  `A_Ω = ∑_{ab}(δ_ab−p) y_ab ⊗ y_ab`,
`y_ab = P_T(e_a e_b*)`,  `sR = √(log(max n₁ n₂)/p)·R`.
-/
theorem rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ ab : Fin n₁ × Fin n₂,
                  (((if ab ∈ Omega then (1 : ℝ) else 0)
                      - (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) •
                    Matrix.vecMulVec
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2)
                          e.1 e.2)))))‖) ≤
          Csym *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R)
          * bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                Real.sqrt
                  (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                      (∑ ab : Fin n₁ × Fin n₂,
                        (if ab ∈ Omega then (1 : ℝ) else 0) •
                          Matrix.vecMulVec
                            (fun e : Fin n₁ × Fin n₂ =>
                              tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                            (fun e : Fin n₁ × Fin n₂ =>
                              tangentProjection S (coordinateMatrix ab.1 ab.2)
                                e.1 e.2))))‖)) := by
  sorry
