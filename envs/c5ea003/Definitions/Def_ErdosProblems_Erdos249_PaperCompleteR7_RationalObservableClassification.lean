-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_RationalObservableClassification
-- name    : ErdosProblems_Erdos249_PaperCompleteR7_RationalObservableClassification
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T12:34:54.405025+00:00
-- url     : https://prove2.me/theorems/391c331a-7c7c-4be7-8b69-72978cf6f2a4
-- title:
--   Rational-valued totient observables
-- statement:
--   Defines the positive-index rational totient observable and its relation to the centred integer-valued series, retaining the correct zero-index convention.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR7/RationalObservableClassification.lean#L1-L80

import Definitions.Def_ErdosProblems_Erdos249_ResidueClassTotientSeries
import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

/-!
# Rational-valued dyadic observables: the missing paper assembly

Targets: short-note `res:residueseries`; long-record
`thm:dyadic-classification`, and the sharpness clause of
`thm:residueobservable`.

`positiveValue` subtracts the n=0 contribution explicitly.  The integer
observable in the imported library includes n=0 and assumes f(0)=0;
confusing these conventions would give the wrong rational-value formula.

The proof clears finitely many rational denominators, invokes the existing
integer-observable theorem, and evaluates the eventually constant tail.
No new CRT, Dirichlet, or isolated-pulse hypothesis is assumed.
Build status: NOT RUN; all declarations below are complete proof candidates.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables

open scoped BigOperators

/-- Full n>=0 series minus its n=0 coefficient: the paper's n>=1 sum. -/
noncomputable def positiveValue (f : ℕ → ℚ) (m : ℕ) : ℝ :=
  (∑' n : ℕ, (f (Nat.totient n % m) : ℝ) / 2 ^ n) - (f 0 : ℝ)




































end ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables


