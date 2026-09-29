-- Prove2me | Theorems.Thm_lean_workbook_plus_50821
-- name    : lean_workbook_plus_50821
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/10c30b68-9550-407e-8630-62913fd6b045
-- statement:
--   Then use the Stars and Bars formula $\binom{n+k-1}{n}$ . Where $n$ is the stars and $k$ is the bars. Then just do $\binom{14}{5}=\boxed{2002}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50821 Nat.choose 14 5 = 2002   :=  by sorry
