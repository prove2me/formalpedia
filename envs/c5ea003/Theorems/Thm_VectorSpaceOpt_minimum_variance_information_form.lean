-- Prove2me | Theorems.Thm_VectorSpaceOpt_minimum_variance_information_form
-- name    : VectorSpaceOpt.minimum_variance_information_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:27:52.001509+00:00
-- url     : https://prove2.me/theorems/60a879e0-a8c0-442f-83d1-4d8e81efc187
-- title:
--   Information form of the minimum-variance gain and error covariance
-- statement:
--   Let $W$ be an $m \times n$ matrix and let $Q$ ($m \times m$) and $R$ ($n \times n$) be **positive definite**. Then the following two matrix identities hold:
--
--   $$R W^\top \big(W R W^\top + Q\big)^{-1} \;=\; \big(W^\top Q^{-1} W + R^{-1}\big)^{-1} W^\top Q^{-1},$$
--
--   $$R - R W^\top \big(W R W^\top + Q\big)^{-1} W R \;=\; \big(W^\top Q^{-1} W + R^{-1}\big)^{-1}.$$
--
--   The left-hand sides are the gain and error covariance of the minimum-variance estimate in the measurement model $y = W\beta + \varepsilon$, with $R$ the prior covariance of $\beta$ and $Q$ that of the noise; the right-hand sides are the same quantities in **information form**, so called because they are expressed through the inverse covariances $Q^{-1}$ and $R^{-1}$.
--
--   The identity matters for comparison: as $R^{-1} \to 0$ — infinite prior variance, meaning no prior information about $\beta$ — the right-hand sides reduce to $(W^\top Q^{-1} W)^{-1} W^\top Q^{-1}$ and $(W^\top Q^{-1} W)^{-1}$, which are exactly the Gauss–Markov gain and covariance. The Gauss–Markov estimate is thus a limiting case of the minimum-variance estimate. The proof is direct: premultiply by $(W^\top Q^{-1} W + R^{-1})$ and postmultiply by $(W R W^\top + Q)$.
--
--   **Formalization Note.** A statement about matrices only; positive definiteness (which includes symmetry) is what guarantees the inverses exist.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.5, Corollary 2, p. 90

import Mathlib
open Matrix

namespace VectorSpaceOpt

theorem minimum_variance_information_form {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) :
    R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ = (Wᵀ * Q⁻¹ * W + R⁻¹)⁻¹ * Wᵀ * Q⁻¹ ∧
    R - R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ * W * R = (Wᵀ * Q⁻¹ * W + R⁻¹)⁻¹ := by sorry

end VectorSpaceOpt
