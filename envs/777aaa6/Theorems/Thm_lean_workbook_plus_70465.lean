-- Prove2me | Theorems.Thm_lean_workbook_plus_70465
-- name    : lean_workbook_plus_70465
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4cdfe1a5-825b-4b12-9a81-5a1e8821b9bf
-- statement:
--   Show that $7^{100} \equiv 1 \pmod{100}$ using the fact that $7^4 \equiv 1 \pmod{100}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70465 : 7 ^ 100 ≡ 1 [ZMOD 100]   :=  by sorry
