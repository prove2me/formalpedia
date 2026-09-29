-- Prove2me | Theorems.Thm_lean_workbook_plus_68238
-- name    : lean_workbook_plus_68238
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c3a16d98-9e15-4cea-9480-85328496b67e
-- statement:
--   $a \vdots 30 \iff 30 \mid a$, as I know.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68238 (a : ℤ) : 30 ∣ a ↔ a ≡ 0 [ZMOD 30]   :=  by sorry
