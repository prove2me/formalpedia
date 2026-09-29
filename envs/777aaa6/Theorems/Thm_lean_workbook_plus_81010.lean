-- Prove2me | Theorems.Thm_lean_workbook_plus_81010
-- name    : lean_workbook_plus_81010
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/eb5ccc27-a1f0-4e16-8f71-cf660d9e9811
-- statement:
--   Let $a,m$ be coprime integers. Show that $\forall a$ there exist $x$ with $ax \equiv 1 (\mod m)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81010 {a m : ℤ} (h : a.gcd m = 1) : ∃ x, a * x ≡ 1 [ZMOD m]   :=  by sorry
