-- Prove2me | Theorems.Thm_lean_workbook_plus_27514
-- name    : lean_workbook_plus_27514
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2db36cbb-5962-46bb-aa4b-4a60fc14c1fd
-- statement:
--   $\sigma(n)=\sum\limits_{d|n}d=\sum\limits_{d|n}\frac{n}{d}=n\sum\limits_{d|n}\frac{1}{d}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27514 (n : ℕ) : ∑ d in n.divisors, d = ∑ d in n.divisors, n/d   :=  by sorry
