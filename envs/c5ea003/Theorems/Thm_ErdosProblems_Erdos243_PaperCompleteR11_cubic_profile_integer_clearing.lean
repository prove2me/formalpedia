-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_profile_integer_clearing
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_profile_integer_clearing
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:34:31.100358+00:00
-- url     : https://prove2.me/theorems/21f49a37-96fb-44df-aca9-43ae91c7e0cc
-- title:
--   Lean source theorem: cubic_profile_integer_clearing
-- statement:
--   For any rational κ and η, there are integers q>0, A and B such that q[κk(k+1)(k+2)+η]=Ak(k+1)(k+2)+B for every natural k; if κ is nonzero, A is nonzero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicWindowTransport.lean#L19-L54
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/-!
# From actual modular cubic roots to the exceptional-set density

Rational profile coefficients are cleared over the
integers before reduction. There is deliberately no ring homomorphism from
`ℚ` to `ZMod p`. The final theorem is conditional on an actual divergent family
of good primes; producing that family from a number-field nonsquare remains a
separate global obligation, not a premise silently claimed to have been proved.
-/


open scoped BigOperators

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_profile_integer_clearing (κ η : ℚ) :
    ∃ q A B : ℤ, 0 < q ∧
      (∀ n : ℕ, (q : ℚ) *
        (κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η) =
        (A : ℚ) * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + (B : ℚ)) ∧
      (κ ≠ 0 → A ≠ 0) := by sorry
