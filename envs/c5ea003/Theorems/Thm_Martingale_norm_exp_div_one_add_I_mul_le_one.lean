-- Prove2me | Theorems.Thm_Martingale_norm_exp_div_one_add_I_mul_le_one
-- name    : Martingale.norm_exp_div_one_add_I_mul_le_one
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:07:28.884002+00:00
-- url     : https://prove2.me/theorems/67c1544d-97a6-44b1-9976-a572eaa9b709
-- title:
--   Each factor of $J^{(2)}$ has modulus at most one
-- statement:
--   For real $\theta$ and $z$,
--
--   $$\left|\frac{e^{i\theta z}}{1 + i\theta z}\right| \le 1 .$$
--
--   Both halves are immediate. The numerator has modulus exactly $1$, being the exponential of a purely imaginary number. The denominator has modulus at least $1$, since $|1 + i\theta z|^2 = 1 + \theta^2z^2 \ge 1$ — the real part is exactly $1$ and the imaginary part exactly $\theta z$. In particular the denominator never vanishes, so the quotient is always defined and no side condition is needed.
--
--   **Where it is used.** McLeish's proof decomposes $e^{i\theta S_n} = J^{(1)}_nJ^{(2)}_n$ and, after factorising, $J^{(2)}_n = \prod_{k<n} e^{i\theta Z_k}/(1 + i\theta Z_k)$. The aggregation step — which converts per-factor estimates into a bound on the difference of two products — requires all factors to have modulus at most $1$, since otherwise perturbations compound multiplicatively rather than adding. This lemma supplies that hypothesis for the factors of $J^{(2)}_n$; the comparison factors $e^{-\theta^2Z_k^2/2}$ satisfy it trivially, being exponentials of nonpositive reals.
--
--   It also yields $|J^{(2)}_n| \le 1$ for the whole product, which together with the boundedness of $J^{(1)}_n$ after truncation is what makes the error term uniformly integrable.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

theorem Martingale.norm_exp_div_one_add_I_mul_le_one (θ z : ℝ) :
    ‖Complex.exp (Complex.I * θ * (z : ℂ)) / (1 + Complex.I * θ * (z : ℂ))‖ ≤ 1 := by sorry
