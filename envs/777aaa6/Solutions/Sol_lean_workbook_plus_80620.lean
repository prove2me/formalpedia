-- Prove2me | solution 1 for lean_workbook_plus_80620
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:57:14.628347+00:00
-- url     : https://prove2.me/submissions/28fd16de-3ca4-454a-be5e-4aaea12c8b2d

import Mathlib.Tactic

theorem solution {m : ℤ} : (m^2 - 1) * (m^2 + 2) = (m^2 - 1)^2 + 3 * (m^2 - 1) := by ring
