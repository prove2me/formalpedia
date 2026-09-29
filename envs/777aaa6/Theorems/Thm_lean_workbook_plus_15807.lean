-- Prove2me | Theorems.Thm_lean_workbook_plus_15807
-- name    : lean_workbook_plus_15807
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6b6997ee-9e2d-4a5a-94c5-6073c3c7cb80
-- statement:
--   Simplify $\left(\frac{1}{3}+\frac{1}{5}\right)+\left(\frac{1}{3^2}+\frac{1}{5^2}\right)+\cdots+\left(\frac{1}{3^n}+\frac{1}{5^n}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15807 (n : ℕ) : (∑ k in Finset.Icc 1 n, (1 / (3 ^ k) + 1 / (5 ^ k))) = (∑ k in Finset.Icc 1 n, 1 / (3 ^ k)) + (∑ k in Finset.Icc 1 n, 1 / (5 ^ k))   :=  by sorry
