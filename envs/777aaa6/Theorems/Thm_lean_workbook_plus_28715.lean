-- Prove2me | Theorems.Thm_lean_workbook_plus_28715
-- name    : lean_workbook_plus_28715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4c12a9a6-6d4e-4a26-98a8-5289688ee540
-- statement:
--   Suppose $ A$ , $ B$ , and $ C$ are three numbers for which $ 1001C - 2002A = 4004$ and $ 1001B + 3003A = 5005$ .The average of the three numbers $ A$ , $ B$ , and $ C$ is\n\n $ \text{(A)}\ 1 \qquad \text{(B)}\ 3 \qquad \text{(C)}\ 6 \qquad \text{(D)}\ 9 \qquad \text{(E)}\ \text{not uniquely determined}$\n\nDividing by 1001 for the first equation results in $ C-2A=4$ . Dividing by 1001 for the second equation results in $ B+3A=5$ . Adding both equations gives us $ A+B+C=9$ , so the average is $ 3$ , or $ B$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28715  (a b c : ℝ)
  (h₀ : 1001 * c - 2002 * a = 4004)
  (h₁ : 1001 * b + 3003 * a = 5005) :
  (a + b + c) / 3 = 3   :=  by sorry
