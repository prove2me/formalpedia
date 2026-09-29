-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_coprime_sumSquares_square_dvd48
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.coprime_sumSquares_square_dvd48
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:46:44.013126+00:00
-- url     : https://prove2.me/theorems/0d7e9bd2-4a33-42ed-9731-3567063c9533
-- title:
--   Coprime positive pair under the 48 divisibility bound
-- statement:
--   If positive coprime natural numbers r and s satisfy (r² + s²)² dividing 48, then r = s = 1.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicScaleArithmetic.lean#L17-L42
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

                                                                    
                                                                           
                                         

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.coprime_sumSquares_square_dvd48
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime r s) (hd : (r ^ 2 + s ^ 2) ^ 2 ∣ 48) :
    r = 1 ∧ s = 1 := by sorry
