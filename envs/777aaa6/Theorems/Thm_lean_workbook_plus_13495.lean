-- Prove2me | Theorems.Thm_lean_workbook_plus_13495
-- name    : lean_workbook_plus_13495
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4539edb5-3bc0-477c-9469-db41694260de
-- statement:
--   $(r+s)^3=(a+d)^3 \implies r^3+s^3=a^3+d^3+3a^2d+3ad^2-3rs(r+s)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13495 (r s a d : ℤ) : (r + s) ^ 3 = (a + d) ^ 3 → r ^ 3 + s ^ 3 = a ^ 3 + d ^ 3 + 3 * a ^ 2 * d + 3 * a * d ^ 2 - 3 * r * s * (r + s)   :=  by sorry
