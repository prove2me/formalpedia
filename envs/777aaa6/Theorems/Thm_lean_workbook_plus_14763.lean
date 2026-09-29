-- Prove2me | Theorems.Thm_lean_workbook_plus_14763
-- name    : lean_workbook_plus_14763
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/debf8682-2757-4bb8-96b1-bf688f491b6c
-- statement:
--   For a certain function $f(x)$ , $f(x+y) = f(xy)-f(x)+f(-y)$ for all reals $x$ and $y$ . Given that $f(-1) = 5$ , find $f(2022)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14763 (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f (x*y) - f x + f (-y)) : f (-1) = 5 → f 2022 = 5   :=  by sorry
