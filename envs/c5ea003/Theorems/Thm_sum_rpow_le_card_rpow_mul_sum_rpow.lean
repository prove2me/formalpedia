-- Prove2me | Theorems.Thm_sum_rpow_le_card_rpow_mul_sum_rpow
-- name    : sum_rpow_le_card_rpow_mul_sum_rpow
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T02:41:37.405125+00:00
-- url     : https://prove2.me/theorems/f1a10c85-06e8-4d0a-b411-0534f5f0ad7c
-- statement:
--   **Singular-value power-mean inequality.** For a nonnegative finite vector $\sigma : \operatorname{Fin} N \to \mathbb{R}$ and exponents $0 < q \le s$: $\sum_k \sigma_k^q \le N^{1 - q/s}\,\big(\sum_k \sigma_k^s\big)^{q/s}$. This is the $\ell_q \le \ell_s$ power-mean bound (with the count factor $N^{1-q/s}$) that bridges an even Schatten moment $\sum \sigma^{2n}$ to a general-$q$ Schatten moment $\sum \sigma^q$ in the Rudelson / Candes-Recht Sec 6.1 noncommutative-Khintchine reduction; the $N^{1-q/s}$ dimension factor is then absorbed by the window $N^{1/q} \le e$ for $q \ge \log N$. Proof: the weighted Holder inequality with weight $\equiv 1$ and exponent $p = s/q \ge 1$.
-- source:
--   Hardy-Littlewood-Polya, Inequalities (CUP 1952), power-means; the weighted Holder inequality (Real.inner_le_weight_mul_Lp_of_nonneg, weight ≡ 1, exponent s/q). Candes-Recht 2009 (arXiv:0805.4471) Sec 6.1: the analytic step bridging the EVEN Schatten moment ∑σ^{2n} to a general-q Schatten moment ∑σ^q in the noncommutative-Khintchine reduction.

import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic
open scoped BigOperators

theorem sum_rpow_le_card_rpow_mul_sum_rpow {N : ℕ} (σ : Fin N → ℝ) (hσ : ∀ k, 0 ≤ σ k) (q s : ℝ) (hq : 0 < q) (hqs : q ≤ s) : (∑ k, (σ k) ^ q) ≤ (N : ℝ) ^ (1 - q / s) * (∑ k, (σ k) ^ s) ^ (q / s) := by sorry
