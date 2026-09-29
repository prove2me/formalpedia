-- Prove2me | Theorems.Thm_lean_workbook_plus_14201
-- name    : lean_workbook_plus_14201
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/78eca60e-aa27-4343-a99a-714564efdce6
-- statement:
--   $\frac{f(a)+f(b)}{2}+\frac{f(b)+f(c)}{2}+\frac{f(c)+f(a)}{2}\geq f(\frac{a+b}{2})+f(\frac{b+c}{2})+f(\frac{c+a}{2})\Rightarrow \frac{1}{a}+\frac{1}{b}+\frac{1}{c}\geq \frac{2}{a+b}+\frac{2}{b+c}+\frac{2}{c+a}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14201 (f : ℝ → ℝ) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (f a + f b) / 2 + (f b + f c) / 2 + (f c + f a) / 2 ≥ f (a + b) / 2 + f (b + c) / 2 + f (c + a) / 2 → 1 / a + 1 / b + 1 / c ≥ 2 / (a + b) + 2 / (b + c) + 2 / (c + a)   :=  by sorry
