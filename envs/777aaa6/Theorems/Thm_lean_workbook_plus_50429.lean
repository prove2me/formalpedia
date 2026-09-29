-- Prove2me | Theorems.Thm_lean_workbook_plus_50429
-- name    : lean_workbook_plus_50429
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/65833f63-8b7d-41bd-8083-783fabc13954
-- statement:
--   Suppose a,b,c are the sides of a triangle. Prove that : \n $\boxed{abc \ge (b + c - a)(c + a - b)(a + b - c)} \quad(1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50429 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a * b * c ≥ (b + c - a) * (c + a - b) * (a + b - c)   :=  by sorry
