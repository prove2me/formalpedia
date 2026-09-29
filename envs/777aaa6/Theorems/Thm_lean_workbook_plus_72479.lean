-- Prove2me | Theorems.Thm_lean_workbook_plus_72479
-- name    : lean_workbook_plus_72479
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/08d2ba1f-7335-4ab4-9b49-fd078b891e92
-- statement:
--   Let $z_1 = p+qi$ and $z_2 = r+si$ , then \n\n $|z_1+2z_2| = |2z_1+z_2| \implies |(p+2r) + i(q+2s)| = |(2p+r) + i(2q+s)|$ \n\n $\implies \sqrt{(p+2r)^2 + (q+2s)^2} = \sqrt{(2p+r)^2 + (2q+s)^2}$ \n\n $\implies r^2 + s^2 = p^2 + q^2 $ \n\nor equivalently, $|z_1| = |z_2|$ . \n\nTherefore, we have that \n\n $(a^2-1)(r^2+s^2) = (a^2-1)(p^2+q^2)$ \n\n $\implies (p^2 +2apr+ a^2r^2) + (q^2 + 2asq + a^2s^2) = (a^2p^2 + 2apr + r^2 )+ (a^2q^2+2aqs+s^2)$ \n\n $\implies \sqrt{(p+ar)^2 + (q+as)^2} = \sqrt{(ap+r)^2 + (aq+s)^2}$ \n\n $\implies |z_1 + az_2| = |az_1+z_2|$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72479  (p q r s a : ℝ)
  (h₀ : 0 < a)
  (h₁ : r^2 + s^2 = p^2 + q^2)
  (h₂ : (p^2 + 2 * a * p * r + a^2 * r^2) + (q^2 + 2 * a * q * s + a^2 * s^2) = (a^2 * p^2 + 2 * a * p * r + r^2) + (a^2 * q^2 + 2 * a * q * s + s^2)) :
  (p + a * r)^2 + (q + a * s)^2 = (a * p + r)^2 + (a * q + s)^2   :=  by sorry
