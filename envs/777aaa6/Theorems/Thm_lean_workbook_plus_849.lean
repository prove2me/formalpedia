-- Prove2me | Theorems.Thm_lean_workbook_plus_849
-- name    : lean_workbook_plus_849
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/feb5e952-fccd-4d3f-aaa4-95582daba7fc
-- statement:
--   We want $3n+45$ to be equal to $16$ (mod $1060$ ). This leads us to set up an equation: \n $$3n+45=16+1060x \implies$$ $$3(n+15)=3(5+353x)+x+1$$ Since $n$ must be an integer the RHS must be divisible by $3$ . From the factorization above we clearly only need $x+1$ to be divisible by $3$ (since the rest already is). Obviously, the smallest such positive value is $x=2$ . Plugging that back in we have: \n $$3n+45=16+2120 \implies$$ $$3n+45=2136 \implies$$ $$n=697$$ This makes $18n+17=12563$ , which in mod $1920$ is $\boxed{1043}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_849 :
  (18 * 697 + 17) % 1920 = 1043   :=  by sorry
