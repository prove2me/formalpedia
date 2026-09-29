-- Prove2me | solution 1 for lean_workbook_plus_43373
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:24.088311+00:00
-- url     : https://prove2.me/submissions/9a665f67-d1a2-47be-bee1-b51fcde5a6aa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c m_b m_c : ℝ) : (2 / 3 * m_b + 1 / 3 * m_c > 1 / 2 * c ∧ 2 / 3 * m_c + 1 / 3 * m_b > 1 / 2 * b) → 2 * (m_b + m_c) > b + c := by
  (intros; linarith)
