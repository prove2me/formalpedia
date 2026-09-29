-- Prove2me | Theorems.Thm_lean_workbook_plus_39580
-- name    : lean_workbook_plus_39580
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/855afa0b-5c8e-49a3-8080-becd56d44fac
-- statement:
--   Find the value of \n(ii) ${\binom{50}{0}}^2+{\binom{50}{1}}^2+{\binom{50}{2}}^2+ \cdots +{\binom{50}{49}}^2+{\binom{50}{50}}^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39580 : ∑ i in Finset.range 51, (Nat.choose 50 i)^2 = 10089134454556419375   :=  by sorry
