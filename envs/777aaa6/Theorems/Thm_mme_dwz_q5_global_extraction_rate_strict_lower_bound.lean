-- Prove2me | Theorems.Thm_mme_dwz_q5_global_extraction_rate_strict_lower_bound
-- name    : mme_dwz_q5_global_extraction_rate_strict_lower_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T18:12:27.182006+00:00
-- url     : https://prove2.me/theorems/2165c756-42bd-4875-b42e-c2b2528dfb64
-- title:
--   The original q=5 global extraction rate exceeds 1.4905135
-- statement:
--   The concrete asymptotic extraction rate of the released q=5 fourth-power global profile is strictly greater than 14905135/10000000. This uses the actual target-count, X/Y marginal, and pooled compatibility entropy expressions, without an assumed global extraction premise. Exact rational cell distributions identify the three branches with the accepted retained-entropy certificate; its common floor is 1490513549769/1000000000000.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.3, Equation (25), and Table 3; https://arxiv.org/abs/2210.10173v5. Specialization to the released q=5 fourth-power witness and original prescribed Z profiles.

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
set_option autoImplicit false

theorem mme_dwz_q5_global_extraction_rate_strict_lower_bound : (14905135 / 10000000 : ℝ) < MME.DWZQ5AsymptoticData.extractionRate := by sorry
