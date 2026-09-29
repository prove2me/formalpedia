-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_isSquare_square_mul_iff
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.isSquare_square_mul_iff
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:54:11.412039+00:00
-- url     : https://prove2.me/theorems/61c16a4f-4895-4d07-8f05-5765ab405804
-- title:
--   Lean source theorem: isSquare_square_mul_iff
-- statement:
--   In any field, multiplying an element γ by the square of a nonzero c leaves its square status unchanged: c²γ is a square exactly when γ is a square.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/FrobeniusDescent.lean#L45-L58
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.isSquare_square_mul_iff {K : Type*} [Field K]
    (c γ : K) (hc : c ≠ 0) : IsSquare (c ^ 2 * γ) ↔ IsSquare γ := by sorry
