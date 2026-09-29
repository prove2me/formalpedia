-- Prove2me | Theorems.Thm_lean_workbook_plus_81212
-- name    : lean_workbook_plus_81212
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/349cd484-a40e-4218-ad06-3e1666175994
-- statement:
--   Let $x$ , $y$ be real numbers. Show that $x \leq y+\epsilon$ for all real numbers $\epsilon >0$ (for every $\epsilon>0)$ if and only if $x \leq y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81212 (x y : ℝ) (h : ∀ ε : ℝ, ε > 0 → x ≤ y + ε) : x ≤ y   :=  by sorry
