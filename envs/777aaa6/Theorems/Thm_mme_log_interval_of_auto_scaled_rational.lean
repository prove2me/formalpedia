-- Prove2me | Theorems.Thm_mme_log_interval_of_auto_scaled_rational
-- name    : mme_log_interval_of_auto_scaled_rational
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T15:00:30.408548+00:00
-- url     : https://prove2.me/theorems/c7cb4155-315b-4ee6-9257-85abd52b1adc
-- title:
--   Logarithm interval of a positive rational from a scale and a term count
-- statement:
--   For a positive rational $q$ and a scale $k$ with $q\,2^k \ge 1$, write
--
--   $$t = \frac{q\,2^k - 1}{q\,2^k + 1}, \qquad S_n = \sum_{i<n} \frac{t^{2i+1}}{2i+1},$$
--
--   so that $\log(q\,2^k) = 2\,\mathrm{artanh}(t)$ and $S_n$ is the truncated series. Define
--
--   $$L(q,k,n) = 2 S_n - k\,\frac{69314718057}{10^{11}}, \qquad U(q,k,n) = 2\Big(S_n + \frac{t^{2n+1}}{1-t^2}\Big) - k\,\frac{69314718055}{10^{11}} .$$
--
--   Then
--
--   $$L(q,k,n) \;\le\; \log q \;\le\; U(q,k,n).$$
--
--   The two decimal constants bracket $\log 2$ from above and below, so subtracting $k$ of them undoes the scaling in the safe direction on each side; the tail $t^{2n+1}/(1-t^2)$ dominates the remainder of the alternating-free series.
--
--   The point of this form is that a table of logarithms needs to record only a rational $q$ and a scale $k$: positivity and $q\,2^k \ge 1$ are the only facts to check, and the interval endpoints are then *computed* from $q$, $k$ and the term count rather than stored as independent data that would have to be trusted or separately certified.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_auto_scaled_log_interval_data
import Mathlib.Tactic

open MME BigOperators Finset

set_option autoImplicit false

theorem mme_log_interval_of_auto_scaled_rational
    (q : ℚ) (k n : ℕ) (hq : 0 < q) (hscaleLower : 1 ≤ q * 2 ^ k) :
    (autoScaledLogLower q k n : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ (autoScaledLogUpper q k n : ℝ) := by sorry
