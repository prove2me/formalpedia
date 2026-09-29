-- Prove2me | Theorems.Thm_lean_workbook_plus_56999
-- name    : lean_workbook_plus_56999
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/9fa86ed0-ade1-4855-8260-d6a8a7cbedcf
-- statement:
--   For $x \equiv 0 \pmod{3}$, you get $x^2 \equiv 0^2 \pmod{3} => x^2 \equiv 0 \pmod{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56999 {x : ℤ} (hx : x ≡ 0 [ZMOD 3]) : x^2 ≡ 0 [ZMOD 3]   :=  by sorry
