-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_integral_coefficients_of_four_agreements
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_integral_coefficients_of_four_agreements
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:31:51.647427+00:00
-- url     : https://prove2.me/theorems/e7513089-9d38-470f-884d-6c66ec2ca3a3
-- title:
--   Lean source theorem: cubic_integral_coefficients_of_four_agreements
-- statement:
--   If an integer sequence agrees at four consecutive indices starting at n with κ·k(k+1)(k+2)+η, then 6κ and η are integers m and c, and the rational cubic equals m times the rising binomial coefficient plus c at every natural index.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicIntegralNormalisation.lean#L37-L75
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Integral normalisation at the quarter-density threshold

The integral coefficients are
constructed from one clean four-window. In particular they are conclusions,
not hidden hypotheses in an arbitrary rational-profile statement.
- A non-integral constant or non-integral third difference gives density >= 1/4.
- The argument needs only an integer-valued sequence, not a recurrence.
- No claim that an integral constant must be +1 or -1 is made here.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_integral_coefficients_of_four_agreements
    (C : ℕ → ℤ) (κ η : ℚ) (n : ℕ)
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) =
      κ * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) *
        (((n + j : ℕ) : ℚ) + 2) + η) :
    ∃ m c : ℤ, (m : ℚ) = 6 * κ ∧ (c : ℚ) = η ∧
      ∀ k : ℕ, κ * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + η =
        ((m * risingBinomial k + c : ℤ) : ℚ) := by sorry
