-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
-- name    : ErdosProblems_Erdos1049_G02ArithmeticR16
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:46:13.803196+00:00
-- url     : https://prove2.me/theorems/3863aac6-1681-4422-a5e7-57c71e008b57
-- title:
--   G02 arithmetic suppliers: the summatory totient with an explicit error
-- statement:
--   Möbius inversion and an absolutely convergent divisor sum yield the explicit summatory-totient error for all nonnegative real cutoffs. The submitted module contains the source declarations zetaTwoR16, muSeriesR16, totientConstantR16, totientPrefixR16, totientErrorR16, among others. Source topic: G02 arithmetic suppliers: the summatory totient with an explicit error.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/G02ArithmeticR16.lean#L20-L438
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# G02 arithmetic suppliers: the summatory totient with an explicit error

Proves |Σ_{d≤y} φ(d) - (3/π²)y²| ≤ 2y(1 + log(1+y)) for every real y ≥ 0.
The definitions below are genuine totient/Möbius sums. No asymptotic
supplier is assumed as an axiom, typeclass field, or theorem premise.
-/
namespace ErdosProblems.Erdos1049.PaperR16

open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000

noncomputable def zetaTwoR16 : ℝ := ∑' d : ℕ, (1 : ℝ) / (d : ℝ)^2
noncomputable def muSeriesR16 : ℝ :=
  ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)^2
noncomputable def totientConstantR16 : ℝ := 3 / Real.pi^2
noncomputable def totientPrefixR16 (y : ℝ) : ℝ :=
  ∑ d ∈ Icc 1 ⌊y⌋₊, (d.totient : ℝ)
noncomputable def totientErrorR16 (y : ℝ) : ℝ :=
  2 * y * (1 + Real.log (1 + y))















































end ErdosProblems.Erdos1049.PaperR16


