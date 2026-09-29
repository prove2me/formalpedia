-- Prove2me | Theorems.Thm_lean_workbook_plus_13278
-- name    : lean_workbook_plus_13278
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3bbc42c6-169e-4a68-b181-f6fec4087bf4
-- statement:
--   Prove that $p^4r^2+p^2q^4+q^2r^4\ge p^4qr+ pq^4r+pqr^4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13278 : ∀ {p q r : ℝ}, p^4 * r^2 + p^2 * q^4 + q^2 * r^4 ≥ p^4 * q * r + p * q^4 * r + p * q * r^4   :=  by sorry
