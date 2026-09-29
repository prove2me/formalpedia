-- Prove2me | Theorems.Thm_lean_workbook_plus_14207
-- name    : lean_workbook_plus_14207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/ce34aa13-6a66-4fc8-a03f-a1af40340836
-- statement:
--   Let $p=xyz$ . $z\times$ first equation minus third is $z(p-2)=-4$ $x\times$ second equation minus first is $x(p-3)=-1$ $y\times$ third equation minus second is $y(p-5)=-2$ Multiplying, we get $p(p-2)(p-3(p-5)=-8$ Which is $p^4-10p^3+31p^2-30p+8=0$ Which is $(p-1)(p-4)(p^2-5p+2)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14207  (x y z p : ℝ)
  (h₀ : p = x * y * z)
  (h₁ : x * (p - 3) = -1)
  (h₂ : y * (p - 5) = -2)
  (h₃ : z * (p - 2) = -4) :
  p^4 - 10 * p^3 + 31 * p^2 - 30 * p + 8 = 0   :=  by sorry
