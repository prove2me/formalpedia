-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.zero_middle_neighbour_square
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:59:49.174506+00:00
-- url     : https://prove2.me/submissions/6ccaa402-aab8-4b24-b967-6bff5b54dcdf

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

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution {R : Type*} [CommRing R]
    (w z a d : R) (hzero : a * w - d = 0) (hnext : z = -(a * d)) :
    IsSquare (-w * z) := by
  have hd : d = a * w := (sub_eq_zero.mp hzero).symm
  refine ⟨a * w, ?_⟩
  rw [hnext, hd]
  ring
