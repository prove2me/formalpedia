-- Prove2me | Theorems.Thm_lean_workbook_plus_51722
-- name    : lean_workbook_plus_51722
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9afe7dfb-a50c-4474-bf1b-9690fa587d20
-- statement:
--   For positive real numbers $a, b, w, u$, prove that:\n$ \frac{ab}{a+b} \le \frac{w^2 a+ u^2 b}{(w+u)^2} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51722 (a b w u : ℝ) (ha : 0 < a) (hb : 0 < b) (hw : 0 < w) (hu : 0 < u) : (a * b) / (a + b) ≤ (w^2 * a + u^2 * b) / (w + u)^2   :=  by sorry
