-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_rational_parameter_cleared
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_rational_parameter_cleared
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:34:28.870279+00:00
-- url     : https://prove2.me/theorems/f7842f02-5756-4190-b8ec-b16ff0816cef
-- title:
--   Lean source theorem: cubic_rational_parameter_cleared
-- statement:
--   If m>0, c=±1, and rational W satisfies (W²+1)²=8(6c/m)W³ or (W²+1)²=8(6c/m)W, set s to the absolute numerator and t to the denominator of W in reduced form. Then m(s²+t²)²=48s³t or m(s²+t²)²=48st³.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicRationalScale.lean#L38-L91
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

/-!
# From an actual rational parameter to the integer scale

The numerator and denominator are obtained from the rational itself. In
particular, coprimality and positivity are proved here, not supplied as
additional assumptions on a purported parametrisation.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_rational_parameter_cleared
    (m : ℕ) (c w : ℚ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (heq : (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w^3 ∨
      (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w) :
    m * (w.num.natAbs^2 + w.den^2)^2 =
        48 * w.num.natAbs^3 * w.den ∨
      m * (w.num.natAbs^2 + w.den^2)^2 =
        48 * w.num.natAbs * w.den^3 := by sorry
