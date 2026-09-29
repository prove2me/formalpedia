-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_cubic_residue_window_hit
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_residue_window_hit
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:07:36.582293+00:00
-- url     : https://prove2.me/theorems/b6089b11-989f-40fe-b42a-2a7f160caa5b
-- title:
--   Lean source theorem: rational_cubic_residue_window_hit
-- statement:
--   For integer sequences satisfying the recurrence from T and a rational profile with integer-cleared cubic qP(k)=Ak(k+1)(k+2)+B, suppose modulo prime p that r solves A(r³−r)+B=0, 3Ar≠0 and r²−1 is nonsquare. Every three-index window starting at n≥T with n≡r−2 mod p contains an index where u(k), viewed as rational, differs from P(k).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicWindowTransport.lean#L109-L159
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_residue_window_hit
    (a u v : ℕ → ℤ) (P : ℕ → ℚ) (q A B : ℤ) (T n : ℕ) (hn : T ≤ n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (p : ℕ) [Fact p.Prime] (r : ZMod p)
    (hroot : (A : ZMod p) * (r ^ 3 - r) + (B : ZMod p) = 0)
    (hfactor : 3 * (A : ZMod p) * r ≠ 0)
    (hns : ¬ IsSquare (r ^ 2 - 1)) (hphase : (n : ZMod p) = r - 2) :
    ∃ j : ℕ, j < 3 ∧ (u (n + j) : ℚ) ≠ P (n + j) := by sorry
