-- Prove2me | Theorems.Thm_lean_workbook_plus_77350
-- name    : lean_workbook_plus_77350
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2d3e8f90-2ea5-45f3-b9cd-f081bf94b870
-- statement:
--   The chance that Bob wins can be split into 2 separate cases:\nCase 1: Alice gets last place, and Bob beats Chebychev.\nThe probability of this happening is $\frac{6}{21} \cdot \frac{8}{15} = \frac{16}{105},$ because the last chip drawn has a $\frac{6}{21}$ chance of being red, and the probability that Bob beats Chebychev is $\frac{\binom{14}{7}}{\binom{15}{7}} = \frac{8}{15}.$\nCase 2: Chebychev gets last place, and Bob beats Alice.\nThe probability of this happening is $\frac{8}{21} \cdot \frac{6}{13} = \frac{16}{91},$ since the last chip drawn has a $\frac{8}{21}$ chance of being green, and the probability that Bob beats Alice is $\frac{\binom{12}{7}}{\binom{13}{7}} = \frac{6}{13}.$\nThus, the probability that Bob wins the game is $\frac{16}{91}+\frac{16}{105} = \boxed{\frac{64}{195}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77350 (6/21 * 8/15) + (8/21 * 6/13) = 64/195   :=  by sorry
