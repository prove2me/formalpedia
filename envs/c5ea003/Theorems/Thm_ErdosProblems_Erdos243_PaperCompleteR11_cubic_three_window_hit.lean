-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_three_window_hit
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_three_window_hit
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:02:22.97263+00:00
-- url     : https://prove2.me/theorems/dc57308f-549b-41d9-946c-494c196c9362
-- title:
--   Lean source theorem: cubic_three_window_hit
-- statement:
--   For field-valued sequences satisfying the numerator and denominator recurrences from index T, suppose A(r³−r)+B=0, 3Ar≠0, and r²−1 is nonsquare. If the three-index window starts at n≥T with n=r−2 in the field, at least one of its three numerator values differs from A[(k+1)³−(k+1)]+B.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicWindowTransport.lean#L69-L107
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_three_window_hit {K : Type*} [Field K]
    (u v a : ℕ → K) (A B r : K) (T n : ℕ) (hn : T ≤ n)
    (hnum : ∀ j, T ≤ j → u (j + 1) = a j * u j - v j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hroot : A * (r ^ 3 - r) + B = 0)
    (hfactor : 3 * A * r ≠ 0) (hns : ¬ IsSquare (r ^ 2 - 1))
    (hphase : (n : K) = r - 2) :
    ∃ j : ℕ, j < 3 ∧ u (n + j) ≠
      A * ((((n + j : ℕ) : K) + 1) ^ 3 - (((n + j : ℕ) : K) + 1)) + B := by sorry
