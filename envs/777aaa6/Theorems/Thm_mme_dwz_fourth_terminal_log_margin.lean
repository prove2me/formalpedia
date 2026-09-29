-- Prove2me | Theorems.Thm_mme_dwz_fourth_terminal_log_margin
-- name    : mme_dwz_fourth_terminal_log_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T04:56:41.672638+00:00
-- url     : https://prove2.me/theorems/c447ab2d-c7ab-4969-914a-fe2e7c9b114c
-- title:
--   The terminal logarithm margin of the fourth-power scalar assembly
-- statement:
--   If a real number is at least the rational floor 155673/20000 = 7.78365, then 2401.01 is strictly
--   less than its exponential.
--
--   This is the terminal comparison of the fourth-power assembly: once the recursive construction has
--   been shown to reach a natural-logarithm rate of at least 7.78365, the resulting tensor value
--   exceeds 2401.01, and hence exceeds 2401.
--
--   ```lean
--   ∀ (naturalRate : ℝ) (hRate : (naturalRateFloor : ℝ) ≤ naturalRate),
--     (240101 / 100 : ℝ) < Real.exp naturalRate
--   ```
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_terminal_log_margin_data
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate

open MME MME.DWZFourthScalar
open BigOperators Finset
open scoped Classical

set_option autoImplicit false

theorem mme_dwz_fourth_terminal_log_margin :
    ∀ (naturalRate : ℝ) (hRate : (naturalRateFloor : ℝ) ≤ naturalRate),
    (240101 / 100 : ℝ) < Real.exp naturalRate := by sorry
