-- Prove2me | Theorems.Thm_Martingale_norm_div_sub_le_norm_sub_mul
-- name    : Martingale.norm_div_sub_le_norm_sub_mul
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:16:57.11927+00:00
-- url     : https://prove2.me/theorems/ed452f4b-f185-4961-a9d5-48f8ad80d496
-- title:
--   Clearing a denominator of modulus at least one: $\left\|\frac{u}{z} - w\right\| \le \|u - zw\|$
-- statement:
--   For complex numbers $z, u, w$ with $\|z\| \ge 1$,
--
--   $$\left\|\frac{u}{z} - w\right\| \;\le\; \bigl\|u - z\,w\bigr\| .$$
--
--   The proof is the identity $\frac{u}{z} - w = \frac{u - zw}{z}$ followed by $\|z\| \ge 1$: dividing by a number of modulus at least one can only shrink a distance.
--
--   **Why it is needed.** McLeish's proof of the martingale central limit theorem writes
--   $$e^{i\theta S_n} \;=\; \underbrace{\prod_{k}(1 + i\theta Z_k)}_{J^{(1)}}\cdot \underbrace{\frac{e^{i\theta S_n}}{\prod_k (1 + i\theta Z_k)}}_{J^{(2)}},$$
--   and the second factor $J^{(2)}$ is a *quotient*. Every subsequent estimate — comparing $e^{i\theta z}/(1+i\theta z)$ with $e^{-\theta^2 z^2/2}$ term by term, and then aggregating over $k$ — would otherwise have to be carried out with division present, where the usual product and triangle inequalities do not apply directly.
--
--   This lemma removes the denominator once and for all. Applied with $z = 1 + i\theta Z_k$, whose modulus is $\sqrt{1 + \theta^2 Z_k^2} \ge 1$, it converts each quotient estimate
--   $$\left\|\frac{e^{i\theta Z_k}}{1 + i\theta Z_k} - w\right\| \quad\text{into the division-free}\quad \bigl\|e^{i\theta Z_k} - (1 + i\theta Z_k)\,w\bigr\|,$$
--   which is then handled by the Taylor expansions of $e^{i\theta z}$ and of the comparison factor $w$. The hypothesis $\|z\| \ge 1$ is exactly what the factors $1 + i\theta Z_k$ supply, and it is essential: for $\|z\| < 1$ the inequality reverses.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

theorem Martingale.norm_div_sub_le_norm_sub_mul (z u w : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖u / z - w‖ ≤ ‖u - z * w‖ := by sorry
