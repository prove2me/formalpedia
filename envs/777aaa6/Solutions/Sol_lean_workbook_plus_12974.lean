-- Prove2me | solution 1 for lean_workbook_plus_12974
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:13.786203+00:00
-- url     : https://prove2.me/submissions/73339c9c-7a73-4ba2-989d-f5113fcdb097

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c m_a m_b m_c : ℝ) : a / m_a = b / m_b ∧ b / m_b = c / m_c → a / m_a = c / m_c := by
  (intros; simp_all)
