-- Prove2me | Theorems.Thm_lean_workbook_plus_31411
-- name    : lean_workbook_plus_31411
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a5452f49-3c36-4f21-8c22-1019e227d565
-- statement:
--   Find the smallest integer greater than $4$ that satisfies $x-1 \equiv 0 \pmod{4}$ and $x \equiv 0 \pmod{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31411 (x : ℕ) (hx: x > 4) (h1 : x-1 ≡ 0 [ZMOD 4]) (h2 : x ≡ 0 [ZMOD 3]) : x >= 9   :=  by sorry
