-- Prove2me | solution 1 for lean_workbook_plus_79537
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:50.559368+00:00
-- url     : https://prove2.me/submissions/381390f8-e77e-4e9d-b623-662a855de59e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {ac ab bd gd : ℝ} (h : ab ≠ 0 ∧ ac ≠ 0 ∧ bd ≠ 0 ∧ gd ≠ 0) :
    gd / ac = bd / ab → gd * ab = bd * ac := by
  exact (div_eq_div_iff h.2.1 h.1).mp
