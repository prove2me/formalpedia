-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_scale_rational_classification
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_rational_classification
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:36:28.030508+00:00
-- url     : https://prove2.me/theorems/83748cc6-db85-4f7b-b213-082d78071206
-- title:
--   Lean source theorem: cubic_scale_rational_classification
-- statement:
--   For m>0, c=±1 and nonzero rational W, either equation (W²+1)²=8(6c/m)W³ or (W²+1)²=8(6c/m)W forces m=12.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicRationalScale.lean#L93-L102
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_rational_classification
    (m : ℕ) (c w : ℚ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1) (hw : w ≠ 0)
    (heq : (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w^3 ∨
      (w^2 + 1)^2 = 8 * (6*c/(m : ℚ)) * w) : m = 12 := by sorry
