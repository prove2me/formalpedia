-- Prove2me | Theorems.Thm_lean_workbook_plus_13480
-- name    : lean_workbook_plus_13480
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/13e4aeae-caab-4a79-aac0-530862d2ce11
-- statement:
--   Applying Binomial theorem, we find that $2017^{167} = (2000 + 17)^{167} = \binom{167}{0}2000^{167} + \binom{167}{1}2000^{166} 17 \ldots + \binom{167}{167}17^{167}$ . Note that as we are only interested in the last four digits, we only have to compute $\binom{167}{166}2000^1 17^{166} + \binom{167}{167} 17^{167}$ . Doing some bash yields $\boxed{9073}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13480 :
  (2017^167) % 10000 = 9073   :=  by sorry
