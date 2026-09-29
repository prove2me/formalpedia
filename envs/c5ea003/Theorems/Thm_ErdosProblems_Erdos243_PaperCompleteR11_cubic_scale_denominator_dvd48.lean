-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_scale_denominator_dvd48
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_denominator_dvd48
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:34:29.918976+00:00
-- url     : https://prove2.me/theorems/5251608a-1156-4b6a-b57b-5048de65c7f6
-- title:
--   Lean source theorem: cubic_scale_denominator_dvd48
-- statement:
--   For coprime natural r and s, if m(r²+s²)² equals either 48r³s or 48rs³, then (r²+s²)² divides 48.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicScaleArithmetic.lean#L85-L104
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

                                                                    
                                                                           
                                         

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_denominator_dvd48
    (m r s : ℕ) (hcop : Nat.Coprime r s)
    (heq : m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r ^ 3 * s ∨
      m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r * s ^ 3) :
    (r ^ 2 + s ^ 2) ^ 2 ∣ 48 := by sorry
