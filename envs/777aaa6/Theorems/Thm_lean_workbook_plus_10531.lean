-- Prove2me | Theorems.Thm_lean_workbook_plus_10531
-- name    : lean_workbook_plus_10531
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2bd15b18-a5a8-43e2-8afc-4ed6a39511a5
-- statement:
--   Derive the identity $\binom{n}{i}^2 = \binom{n}{i} \binom{n}{n-i}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10531 (n i : ℕ) : (n.choose i) ^ 2 = n.choose i * n.choose (n - i)   :=  by sorry
