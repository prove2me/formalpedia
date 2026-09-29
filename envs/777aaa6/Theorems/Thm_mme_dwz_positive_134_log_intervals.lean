-- Prove2me | Theorems.Thm_mme_dwz_positive_134_log_intervals
-- name    : mme_dwz_positive_134_log_intervals
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-20T19:51:16.091401+00:00
-- url     : https://prove2.me/theorems/a966689a-f2eb-4b4a-bf36-295f6cab491c
-- title:
--   All 134 logarithm intervals for the concrete DWZ (1,3,4) entropy formula
-- statement:
--   Every one of the 134 rational logarithm certificates in the concrete $(1,3,4)$ entropy data is valid: for each recorded positive rational argument $q_j$, the recorded endpoints satisfy
--   $$\ell_j\le\log q_j\le u_j.$$
--   These intervals cover the nontrivial arguments needed in the coarse, joint parent-word, and non-deterministic compatibility-part entropy expressions. Deterministic compatibility entropies cancel exactly and need no logarithm certificate for their masses. The stated intervals follow from exact rational series certificates checked in Lean.
-- source:
--   mme_dwz_positive_134_entropy_certificate_data; mme_log_interval_of_exact_rational_series_certificate. The arguments are derived from the concrete integer fine-profile data at https://prove2.me/theorems/dcb9191a-b176-4d4d-81f8-b8f2af58386d .

import Definitions.Def_mme_dwz_positive_134_entropy_certificate_data

open BigOperators Finset MME.DWZ134Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mme_dwz_positive_134_log_intervals : ∀ j : Fin 134,
    ((certificates j).lo : ℝ) ≤ Real.log ((certificates j).q : ℝ) ∧
    Real.log ((certificates j).q : ℝ) ≤ ((certificates j).hi : ℝ) := by sorry
