-- Prove2me | Theorems.Thm_Martingale_norm_prod_one_add_I_mul_sq
-- name    : Martingale.norm_prod_one_add_I_mul_sq
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:51:06.920355+00:00
-- url     : https://prove2.me/theorems/212a3c3b-8f67-46df-9621-b0d05124c7f4
-- title:
--   $\left|\prod_k (1 + i\theta Z_k)\right|^2 = \prod_k (1 + \theta^2 Z_k^2)$
-- statement:
--   An exact modulus computation for the auxiliary product that replaces the characteristic function in the martingale central limit theorem. For real $Z_k$ and real $\theta$,
--
--   $$\Bigl|\prod_{k<n} \bigl(1 + i\theta Z_k\bigr)\Bigr|^2 \;=\; \prod_{k<n}\bigl(1 + \theta^2 Z_k^2\bigr).$$
--
--   The modulus of a product is the product of the moduli, and each factor satisfies $|1 + i\theta z|^2 = 1^2 + (\theta z)^2 = 1 + \theta^2 z^2$ since $z$ and $\theta$ are real, so the real part is exactly $1$ and the imaginary part exactly $\theta z$.
--
--   Two consequences drive the McLeish argument, both visible directly from the right-hand side.
--
--   First, every factor is $\ge 1$, so $|J^{(1)}_n| \ge 1$ where $J^{(1)}_n = \prod_k(1 + i\theta Z_k)$. Since $J^{(2)}_n = e^{i\theta\sum_k Z_k}/J^{(1)}_n$ and the numerator has modulus $1$, this gives $|J^{(2)}_n| \le 1$ — the second factor is bounded without any hypothesis at all.
--
--   Second, $1 + x \le e^{x}$ gives
--   $$\bigl|J^{(1)}_n\bigr|^2 \le \exp\Bigl(\theta^2 \sum_{k<n} Z_k^2\Bigr),$$
--   so once the increments have been truncated to keep $\sum_{k<n} Z_k^2$ below a fixed level, $J^{(1)}_n$ is bounded by a constant depending only on $\theta$. Boundedness of both factors is what makes $J^{(1)}_n(J^{(2)}_n - e^{-\theta^2\sigma^2/2})$ uniformly integrable, which is the step that upgrades convergence in probability to convergence of expectations and hence, via Lévy's continuity theorem, to the central limit theorem.
--
--   Note also that $1 + i\theta z$ is never zero for real $z, \theta$ — its real part is $1$ — so the quotient defining $J^{(2)}_n$ is always well defined.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

theorem Martingale.norm_prod_one_add_I_mul_sq {Ω : Type*} (Z : ℕ → Ω → ℝ) (θ : ℝ)
    (n : ℕ) (ω : Ω) :
    ‖∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))‖ ^ 2
      = ∏ k ∈ Finset.range n, (1 + θ ^ 2 * Z k ω ^ 2) := by sorry
