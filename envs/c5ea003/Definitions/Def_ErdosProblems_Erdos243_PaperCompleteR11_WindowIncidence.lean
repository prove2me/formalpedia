-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:57:01.892365+00:00
-- url     : https://prove2.me/theorems/9256d74e-86d9-41c3-9a9d-8d71bc2ab71b
-- title:
--   Lower-density bound predicate
-- statement:
--   Defines LowerDensityAtLeast for a set of natural numbers and a real bound.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/WindowIncidence.lean#L1-L207
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Window incidences and quantitative exceptional density

Every hit is charged to an exceptional index together
with its offset. Overlapping windows therefore cost at most their length, not
the number of residue classes. No density assumption is hidden in the counting
lemmas. `LowerDensityAtLeast` uses the usual epsilon / eventual-prefix definition
of a lower bound for the lower asymptotic density (prefixes start at zero).
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9

/-- Literal eventual-prefix formulation of a lower asymptotic density bound. -/
def LowerDensityAtLeast (E : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    (d - ε) * (X : ℝ) ≤ (exceptionCount E X : ℝ)















end ErdosProblems.Erdos243.PaperCompleteR11


