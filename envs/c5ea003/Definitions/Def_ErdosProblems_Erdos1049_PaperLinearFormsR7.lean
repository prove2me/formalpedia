-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_PaperLinearFormsR7
-- name    : ErdosProblems_Erdos1049_PaperLinearFormsR7
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:45:52.701557+00:00
-- url     : https://prove2.me/theorems/db8681d7-b8ef-478f-bc8b-2875d6562773
-- title:
--   R7: the integer-form irrationality consumer and its polynomial bridge
-- statement:
--   The integer-form consumer converts a supplied cancelled approximation family into irrationality via its exact algebraic identity and decay; this module's consumer has an explicit supply premise where shown. The submitted module contains the source declarations paperLambert, irrational_of_integer_forms_below_every_denominator, irrational_of_integer_forms_tendsto_zero, irrational_of_cancelled_polynomial_forms, CancelledApproximationSupply, among others. Source topic: R7: the integer-form irrationality consumer and its polynomial bridge.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/PaperLinearFormsR7.lean#L24-L142
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinHeightRegion
import Definitions.Def_ErdosProblems_Erdos1049_RationalBaseContour
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# R7: the integer-form irrationality consumer and its polynomial bridge

No axioms and no admitted proofs.

`CancelledApproximationSupply` is an OPEN analytic/source obligation. There is
no declaration asserting that it exists. In particular the conditional region
and power corollaries below are not advertised as proofs of the displayed
unconditional irrationality theorems. The coverage ledger retains that gap.
-/

namespace ErdosProblems.Erdos1049.PaperR7

open Filter
open scoped Topology BigOperators

/-- Precisely the real Lambert value in the paper, indexed from exponent one.
Outside x > 1 this is still Lean's totalised sum; none of the target statements
uses those other inputs. Summability is a separate analytic obligation. -/
noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)







/-- EXACTLY the unproved source-supply step. The definition records all the
integrality and post-cancellation conditions; it does not assume the endpoint
irrationality and does not assert that a source family meeting them exists. -/
def CancelledApproximationSupply (a b : ℕ) : Prop :=
  ∃ (U V : ℕ → Polynomial ℤ) (W : ℕ → ℕ),
    (∀ n, (U n).natDegree ≤ W n) ∧
    (∀ n, (V n).natDegree ≤ W n) ∧
    (∀ᶠ n in atTop,
      (U n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * paperLambert ((a : ℝ) / b) -
        (V n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) ≠ 0) ∧
    Tendsto (fun n => (b : ℝ) ^ (W n) *
      ((U n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * paperLambert ((a : ℝ) / b) -
        (V n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b))) atTop (𝓝 0)



/-- This names the unproved region-wide source construction with the live
contour definition, rather than introducing a rounded replacement constant. -/
def ContourSourceSupply : Prop :=
  ∀ a b : ℕ, 0 < b → b < a → a.Coprime b →
    ZudilinContourRegion a b → CancelledApproximationSupply a b





end ErdosProblems.Erdos1049.PaperR7


