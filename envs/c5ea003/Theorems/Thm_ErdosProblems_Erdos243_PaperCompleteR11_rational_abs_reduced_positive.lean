-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_abs_reduced_positive
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.rational_abs_reduced_positive
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:54:27.954391+00:00
-- url     : https://prove2.me/theorems/db5c25a1-7ed4-4f16-a4d9-5f2a969b3ab6
-- title:
--   Lean source theorem: rational_abs_reduced_positive
-- statement:
--   For nonzero rational W, the absolute value of its reduced numerator is positive, its denominator is positive, those two natural numbers are coprime, and |W| is their quotient.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicRationalScale.lean#L13-L36
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.rational_abs_reduced_positive (w : ℚ) (hw : w ≠ 0) :
    0 < w.num.natAbs ∧ 0 < w.den ∧
      Nat.Coprime w.num.natAbs w.den ∧
      |w| = (w.num.natAbs : ℚ) / (w.den : ℚ) := by sorry
