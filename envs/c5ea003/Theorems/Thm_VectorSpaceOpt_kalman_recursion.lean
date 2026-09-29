-- Prove2me | Theorems.Thm_VectorSpaceOpt_kalman_recursion
-- name    : VectorSpaceOpt.kalman_recursion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:32:59.052145+00:00
-- url     : https://prove2.me/theorems/dd3b3b71-8f27-4718-b100-735397b38a96
-- title:
--   Solution of the recursive estimation problem (Kalman)
-- statement:
--   Work in the Hilbert space of zero-mean random variables, $\langle a, b\rangle = E[ab]$, in which uncorrelated means orthogonal.
--
--   Consider the $n$-dimensional **dynamic model**: a state evolving linearly with noise, observed through a linear measurement with noise,
--
--   $$x(k+1) = \Phi(k)\,x(k) + u(k), \qquad v(k) = M(k)\,x(k) + w(k), \qquad k = 0, 1, 2, \dots$$
--
--   with $\Phi(k)$, $M(k)$ known matrices. The process noises are **white** — $E[u(k)u(l)^\top] = Q(k)\delta_{kl}$ and $E[w(k)w(l)^\top] = R(k)\delta_{kl}$ with each $R(k)$ positive definite — mutually uncorrelated and uncorrelated with the initial state $x(0)$.
--
--   Write $\hat x(k \mid k-1)$ for the estimate of $x(k)$ given the measurements up to time $k-1$. Starting from $\hat x(0 \mid -1) = 0$ and $P(0) = \operatorname{cov} x(0)$, generate estimates and matrices by the recursions
--
--   $$\hat x(k+1 \mid k) = \Phi(k) P(k) M^\top(k)\big[M(k)P(k)M^\top(k) + R(k)\big]^{-1}\big(v(k) - M(k)\hat x(k \mid k-1)\big) + \Phi(k)\,\hat x(k \mid k-1),$$
--
--   $$P(k+1) = \Phi(k) P(k)\Big\{I - M^\top(k)\big[M(k)P(k)M^\top(k) + R(k)\big]^{-1} M(k) P(k)\Big\}\Phi^\top(k) + Q(k).$$
--
--   Then for every $k$:
--
--   1. each component of $\hat x(k \mid k-1)$ lies in the span of the past measurement components $v(0), \dots, v(k-1)$;
--   2. each error component $x(k)_i - \hat x(k \mid k-1)_i$ is orthogonal to every past measurement component;
--   3. the error covariance is $\big\langle x(k)_i - \hat x(k\mid k-1)_i,\ x(k)_j - \hat x(k \mid k-1)_j \big\rangle = P(k)_{ij}$.
--
--   By the projection theorem, claims 1 and 2 say exactly that $\hat x(k \mid k-1)$ *is* the linear minimum-variance estimate of $x(k)$ given the past data — so the recursion computes the optimal estimate, and $P(k)$ tracks its error covariance. This is the discrete-time **Kalman filter**, obtained here with no Gaussian assumption anywhere: only second-order statistics enter, and optimality is among linear estimates.
--
--   **Formalization Note.** The two recursions are supplied as hypotheses defining $\hat x$ and $P$, so the conclusions assert precisely the optimality and covariance claims. Being the optimal estimate is expressed as span membership plus orthogonality of the error rather than through a projection operator. Zero means are implicit in the Hilbert-space-of-random-variables representation, so expectations appear only as inner products.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §4.7, Theorem 1, p. 96; R. E. Kalman, J. Basic Eng. 82 (1960) 35–45, https://doi.org/10.1115/1.3662552

import Mathlib
open Matrix
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem kalman_recursion {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n m : ℕ}
    (Φ : ℕ → Matrix (Fin n) (Fin n) ℝ) (M : ℕ → Matrix (Fin m) (Fin n) ℝ)
    (Q : ℕ → Matrix (Fin n) (Fin n) ℝ) (R : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (hR : ∀ k, (R k).PosDef)
    (x u : ℕ → Fin n → H) (w v : ℕ → Fin m → H)
    (hdyn : ∀ k i, x (k + 1) i = ∑ j, Φ k i j • x k j + u k i)
    (hmeas : ∀ k i, v k i = ∑ j, M k i j • x k j + w k i)
    (hQcov : ∀ k l i j, ⟪u k i, u l j⟫ = if k = l then Q k i j else 0)
    (hRcov : ∀ k l i j, ⟪w k i, w l j⟫ = if k = l then R k i j else 0)
    (huw : ∀ k l i j, ⟪u k i, w l j⟫ = 0)
    (hux0 : ∀ k i j, ⟪u k i, x 0 j⟫ = 0)
    (hwx0 : ∀ k i j, ⟪w k i, x 0 j⟫ = 0)
    (P : ℕ → Matrix (Fin n) (Fin n) ℝ) (xh : ℕ → Fin n → H)
    (hP0 : ∀ i j, P 0 i j = ⟪x 0 i, x 0 j⟫)
    (hxh0 : ∀ i, xh 0 i = 0)
    (hrec : ∀ k i, xh (k + 1) i =
      ∑ j, (Φ k * P k * (M k)ᵀ * (M k * P k * (M k)ᵀ + R k)⁻¹) i j •
          (v k j - ∑ l, M k j l • xh k l) +
        ∑ j, Φ k i j • xh k j)
    (hPrec : ∀ k, P (k + 1) =
      Φ k * P k * (1 - (M k)ᵀ * (M k * P k * (M k)ᵀ + R k)⁻¹ * M k * P k) *
          (Φ k)ᵀ + Q k) :
    (∀ k i, xh k i ∈ Submodule.span ℝ {a : H | ∃ l < k, ∃ j, a = v l j}) ∧
    (∀ k, ∀ l < k, ∀ i j, ⟪x k i - xh k i, v l j⟫ = 0) ∧
    (∀ k i j, ⟪x k i - xh k i, x k j - xh k j⟫ = P k i j) := by sorry

end VectorSpaceOpt
