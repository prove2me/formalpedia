-- Prove2me | Theorems.Thm_lean_workbook_plus_79877
-- name    : lean_workbook_plus_79877
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/9b572624-15bc-42b9-9c7d-e6a6f1f649bd
-- statement:
--   Let's first get rid of the indices and write $a+b+c=p+q+r=ap+bq+cr=0$ . If we consider $b,c,q,r$ as fixed then $a,p$ are defined by $a=-(b+c),p=-(q+r)$ and the ensuing condition is $ap+bq+cr=0\iff 2bq+br+cq+2cr=0$ . Assuming $cr\not=0$ we divide by $cr$ and find $2(b/c)(q/r)+(b/c)+(q/r)+2=0$ . With $\alpha:=b/c,\beta:=q/r$ we have $(2\alpha+1)(2\beta+1)=-3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79877  (a b c p q r : ℝ)
  (h₀ : a + b + c = 0)
  (h₁ : p + q + r = 0)
  (h₂ : a * p + b * q + c * r = 0)
  (h₃ : c ≠ 0) :
  (2 * b * q + b * r + c * q + 2 * c * r = 0)   :=  by sorry
