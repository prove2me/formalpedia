-- Prove2me | Theorems.Thm_binomial_incomplete_beta_at_mean_le_half
-- name    : binomial_incomplete_beta_at_mean_le_half
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T14:17:17.827769+00:00
-- url     : https://prove2.me/theorems/a568b595-fdf3-4fe7-9306-3c358385f9fd
-- title:
--   The incomplete Beta integral at $p=m/N$ is at most $\tfrac12$
-- statement:
--   For $0 \le m < N$, the incomplete Beta integral evaluated at the point $p = m/N$ is at most one half:
--   $$\int_0^{m/N} N\binom{N-1}{m}\, t^m (1-t)^{N-1-m}\, dt \le \tfrac12.$$
--   Equivalently, the cumulative distribution function of the Beta distribution $\mathrm{Beta}(m+1,\,N-m)$ at $m/N$ is at most $1/2$ — i.e. $m/N$ lies at or below the median of $\mathrm{Beta}(m+1,N-m)$. By the binomial-tail = incomplete-beta identity, this is the analytic heart of the integer-mean binomial median theorem (Kaas–Buhrman): it gives $P(X \ge m+1) \le 1/2$ for $X \sim \mathrm{Bin}(N, m/N)$. The integrand $N\binom{N-1}{m}t^m(1-t)^{N-1-m}$ is the $\mathrm{Beta}(m+1,N-m)$ density (it integrates to $1$ over $[0,1]$).
-- source:
--   https://en.wikipedia.org/wiki/Median#Medians_for_samples

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open scoped BigOperators

theorem binomial_incomplete_beta_at_mean_le_half (N m : ℕ) (h : m < N) :
    (∫ t in (0:ℝ)..((m : ℝ) / (N : ℝ)),
        (N : ℝ) * (Nat.choose (N-1) m : ℝ) * t ^ m * (1 - t) ^ (N - 1 - m)) ≤ (1 / 2 : ℝ) := by sorry
