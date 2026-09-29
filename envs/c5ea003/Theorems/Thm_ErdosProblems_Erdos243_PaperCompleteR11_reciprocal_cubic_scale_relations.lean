-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_reciprocal_cubic_scale_relations
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.reciprocal_cubic_scale_relations
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:01.200274+00:00
-- url     : https://prove2.me/theorems/ad2c93b0-dc69-42b2-a8a2-e0bce240a472
-- title:
--   Lean source theorem: reciprocal_cubic_scale_relations
-- statement:
--   In any field, if b,d,W,η satisfy bw+d=0, dw+bd+b=−w, and w²+1+b²+d²=8ηw, then (w²+1)² equals either 8ηw³ or 8ηw.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicScaleArithmetic.lean#L51-L71
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

                                                                    
                                                                           
                                         

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.reciprocal_cubic_scale_relations
    {K : Type*} [Field K] (b d w η : K)
    (h5 : b * w + d = 0)
    (h4 : d * w + b * d + b = -w)
    (h3 : w ^ 2 + 1 + b ^ 2 + d ^ 2 = 8 * η * w) :
    (w ^ 2 + 1) ^ 2 = 8 * η * w ^ 3 ∨
      (w ^ 2 + 1) ^ 2 = 8 * η * w := by sorry
