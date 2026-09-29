-- Prove2me | Theorems.Thm_lean_workbook_plus_44515
-- name    : lean_workbook_plus_44515
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c8829478-9265-4ae0-8530-5a423ba1350a
-- statement:
--   Let $a,b,c,d\geq 0$, prove that: \n$(a+b+c+d)(ac^2b+bd^2c+a^2cd+b^2da)+(b+d)(c+a)(b^2a+c^2b+d^2c+a^2d)-2(b+d)(c+a)(acd+abd+abc+bcd)\geq$ \n$-5(b+d)(c+a)(b^2a+c^2b+d^2c+a^2d)+(a+b+c+d)(d^2+b^2)(c^2+a^2)+(a+b+c+d)(b+d)(c+a)(a^2+c^2+b^2+d^2)\geq$ \n$2(ac+bd)(acd+abd+abc+bcd)+2(b+d)(c+a)(a^3+c^3+b^3+d^3)-3(b+d)(c+a)(b^2a+c^2b+d^2c+a^2d)\geq$ \n$(a+b+c+d)(b^3a+c^3b+d^3c+a^3d)+(a+b+c+d)(ac^2b+bd^2c+a^2cd+b^2da)-2(b+d)(c+a)(acd+abd+abc+bcd)\geq$ \n$(a+b+c+d)(b^3a+c^3b+d^3c+a^3d)+(a+b+c+d)^2(a^2b+b^2c+c^2d+d^2a)-5(b+d)(c+a)(b^2a+c^2b+d^2c+a^2d)\geq$ \n$(a^2+c^2+b^2+d^2)(b^2a+c^2b+d^2c+a^2d)-5(b+d)(c+a)(b^2a+c^2b+d^2c+a^2d)+(a+b+c+d)(b+d)(c+a)(a^2+c^2+b^2+d^2)\geq$ \n$(a+b+c+d)^2(b^2a+c^2b+d^2c+a^2d)-5(b+d)(c+a)(b^2a+c^2b+d^2c+a^2d)+(a+b+c+d)(d^2+b^2)(c^2+a^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44515 ∀ a b c d : ℝ, (a+b+c+d)*(a*c^2*b + b*d^2*c + a^2*c*d + b^2*c*d) + (b+d)*(c+a)*(b^2*a + c^2*b + d^2*c + a^2*d) - 2*(b+d)*(c+a)*(a*c*d + a*b*d + a*b*c + b*c*d) ≥ -5*(b+d)*(c+a)*(b^2*a + c^2*b + d^2*c + a^2*d) + (a+b+c+d)*(d^2 + b^2)*(c^2 + a^2) + (a+b+c+d)*(b+d)*(c+a)*(a^2 + c^2 + b^2 + d^2) ∧ 2*(a*c + b*d)*(a*c*d + a*b*d + a*b*c + b*c*d) + 2*(b+d)*(c+a)*(a^3 + c^3 + b^3 + d^3) - 3*(b+d)*(c+a)*(b^2*a + c^2*b + d^2*c + a^2*d) ≥ (a+b+c+d)*(b^3*a + c^3*b + d^3*c + a^3*d) + (a+b+c+d)*(a*c^2*b + b*d^2*c + a^2*c*d + b^2*c*d) - 2*(b+d)*(c+a)*(a*c*d + a*b*d + a*b*c + b*c*d) ∧ (a+b+c+d)*(b^3*a + c^3*b + d^3*c + a^3*d) + (a+b+c+d)^2*(a^2*b + b^2*c + c^2*d + d^2*a) - 5*(b+d)*(c+a)*(b^2*a + c^2*b + d^2*c + a^2*d) ≥ (a^2 + c^2 + b^2 + d^2)*(b^2*a + c^2*b + d^2*c + a^2*d) - 5*(b+d)*(c+a)*(b^2*a + c^2*b + d^2*c + a^2*d) + (a+b+c+d)*(b+d)*(c+a)*(a^2 + c^2 + b^2 + d^2) ∧ (a+b+c+d)^2*(b^2*a + c^2*b + d^2*c + a^2*d) - 5*(b+d)*(c+a)*(b^2*a + c^2*b + d^2*c + a^2*d) + (a+b+c+d)*(d^2 + b^2)*(c^2 + a^2) ≥ 0   :=  by sorry
