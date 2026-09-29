-- Prove2me | Theorems.Thm_lean_workbook_plus_78367
-- name    : lean_workbook_plus_78367
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/780357fc-34f1-4a55-ad19-c7d90ade1738
-- statement:
--   Note that $\frac{1}{7} = 0.\overline{142857}$ (here, in contrast to above, the overline means repeating, not the number). It is well known that fractions of $7$ simply rotate the digits around. For example, $\frac{2}{7}$ starts with the digit $2$ and equals $0.\overline{285714}$ . If you've never seen this before, go ahead and divide out the other fractions to see! Knowing this, the problem actually becomes very easy if it is short answer. Since $\frac{6}{7} = 6 \cdot \frac{1}{7}$ , and $\frac{6}{7}$ is only a rotation of the digits, specifically $0.\overline{857142}$ , we can find that $6(142857) = 857142$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78367 :
  6 * (142857) = 857142   :=  by sorry
