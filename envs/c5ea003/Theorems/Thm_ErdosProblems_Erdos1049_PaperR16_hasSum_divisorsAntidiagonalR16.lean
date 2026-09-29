-- Prove2me | Theorems.Thm_ErdosProblems_Erdos1049_PaperR16_hasSum_divisorsAntidiagonalR16
-- name    : ErdosProblems.Erdos1049.PaperR16.hasSum_divisorsAntidiagonalR16
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:12:05.974172+00:00
-- url     : https://prove2.me/theorems/df3d00ba-8281-4b45-a87e-5d68229cae6e
-- title:
--   Has sum divisors antidiagonal r16
-- statement:
--   For summable real sequences f,g with f(0)=g(0)=0, their divisor-antidiagonal convolution has sum equal to the product of their sums.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/G02ArithmeticR16.lean#L150-L175
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; the rational-base Lambert-series method follows Zudilin, without a novelty or universal rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Definitions.Def_ErdosProblems_Erdos1049_G02ArithmeticR16
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

open Finset Filter Asymptotics
open scoped BigOperators Topology
set_option maxHeartbeats 2000000

open ErdosProblems.Erdos1049.PaperR16

theorem ErdosProblems.Erdos1049.PaperR16.hasSum_divisorsAntidiagonalR16 (f g : ℕ → ℝ)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hf : Summable f) (hg : Summable g) :
    HasSum (fun n : ℕ => ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2)
      ((∑' a, f a) * (∑' b, g b)) := by sorry
