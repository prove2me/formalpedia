-- Prove2me | Theorems.Thm_lean_workbook_plus_9273
-- name    : lean_workbook_plus_9273
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/6a7ac830-d8c4-48d1-abf2-9374c4e9a78d
-- statement:
--   The answer is $\binom{8}{4}(7!\cdot4!)$ , which is exactly what @ike.chen said. However, I don't think that plain stars and bars works (unless I'm missing something). We first plot the men. MMMMMMM There are 8 possible spots where each woman can go. The women must be be distinct spots, as if they weren't, they would be adjacent. Thus, there are $\binom{8}{4}$ ways to place the women. Since women and men are distinguishable, there are $7!$ ways to order the men and $4!$ ways to order the women. Thus, the answer is $\binom{8}{4}(7!\cdot4!)$ . OP, you're incorrect because you calculated the probability that not all women are together, which is different from only two of them being together.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9273 (Nat.choose 8 4 * 7! * 4!) = 90720   :=  by sorry
