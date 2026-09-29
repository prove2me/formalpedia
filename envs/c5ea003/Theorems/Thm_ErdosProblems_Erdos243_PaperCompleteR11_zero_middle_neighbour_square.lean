-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_zero_middle_neighbour_square
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.zero_middle_neighbour_square
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:56:04.495507+00:00
-- url     : https://prove2.me/theorems/bed89724-d3c1-46cf-a974-7313254867d1
-- title:
--   Lean source theorem: zero_middle_neighbour_square
-- statement:
--   In any commutative ring, if aw=d and z=−ad, then −wz is a square.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/FrobeniusDescent.lean#L89-L97
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos243.PaperCompleteR11
end ErdosProblems.Erdos243.PaperCompleteR11

/-!
# The algebraic descent after a good Frobenius prime is supplied

No prime-existence theorem is declared here. The ordinary number-field
specialisation argument, its finite exceptional set, and the missing formal
Chebotarev dependency are stated explicitly in analytic_proofs.md.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.zero_middle_neighbour_square {R : Type*} [CommRing R]
    (w z a d : R) (hzero : a * w - d = 0) (hnext : z = -(a * d)) :
    IsSquare (-w * z) := by sorry
