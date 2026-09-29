-- Prove2me | Theorems.Thm_lean_workbook_plus_82802
-- name    : lean_workbook_plus_82802
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.51614+00:00
-- url     : https://prove2.me/theorems/8b1818fb-2888-4677-9f86-e236f6d37f42
-- statement:
--   If $a\equiv0(mod b)$ , then $a=bq$ for some integer q. If $a=bq$ , then $b\mid a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82802 (a b : ℤ) : a % b = 0 ↔ b ∣ a   :=  by sorry
