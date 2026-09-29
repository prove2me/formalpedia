-- Prove2me | Theorems.Thm_mme_dwz_q5_coarse_entropy_lower_bounds
-- name    : mme_dwz_q5_coarse_entropy_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T14:03:55.193921+00:00
-- url     : https://prove2.me/theorems/6ed1d9d8-11db-48ce-826b-51a5dd5854a9
-- title:
--   Certified coarse entropy lower bounds for the unchanged q=5 distribution
-- statement:
--   Use the unchanged exact rational-replay $q=5$ fourth-power data. Let $a_c$ be its 45 positive outer component counts, let $s=\sum_c a_c$ be their common scale, and put $\alpha_c=a_c/s$. For each mode $i\in\{0,1,2\}$, let $\alpha_i(g)$ be the corresponding nine-entry marginal distribution. All entropies here use the natural logarithm, with $0\log0=0$.
--
--   The synchronized target-count rate and all three marginal entropies satisfy
--   $$
--   H_T= -\sum_c\alpha_c\log\alpha_c\ge\frac{46}{25},\qquad
--   H_i=-\sum_{g=0}^{8}\alpha_i(g)\log\alpha_i(g)\ge\frac{101}{100}
--   \quad(i=0,1,2).
--   $$
--   The quantity $H_T$ is exactly `targetRate` from the public synchronized-count definition: cancellation of the common denominator-clearing period identifies it with the displayed entropy of the original outer distribution. No profile, count, or marginal is modified.
--
--   These are deliberately coarse certified lower bounds, not numerical approximations of the actual entropy values. The statement alone does not bound compatible competitors, prove positivity of the complete extraction rate, or establish a matrix-multiplication exponent.
-- source:
--   Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Sections 3.6–3.7 and 6.2 (entropy and target/marginal counts). This is a derived exact-data certificate, not a verbatim numbered result. It uses the public q=5 rational-replay profile certificate and mme_log_interval_of_exact_rational_series_certificate (f79fd5f9-9d45-427a-a128-f81b83b98053).

import Definitions.Def_mme_dwz_q5_global_asymptotic_data

set_option autoImplicit false

theorem mme_dwz_q5_coarse_entropy_lower_bounds :
    (46 / 25 : ℝ) ≤ MME.DWZQ5AsymptoticData.targetRate ∧
    ∀ mode : Fin 3, (101 / 100 : ℝ) ≤
      MME.DWZQ5AsymptoticData.marginalEntropy mode := by sorry
