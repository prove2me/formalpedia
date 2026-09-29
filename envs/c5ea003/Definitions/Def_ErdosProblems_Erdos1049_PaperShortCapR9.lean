-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_PaperShortCapR9
-- name    : ErdosProblems_Erdos1049_PaperShortCapR9
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:46:09.272581+00:00
-- url     : https://prove2.me/theorems/4f8b15a5-9d6c-4263-9ddd-c4c8c0cae2c0
-- title:
--   Quadratic short-note irrationality cap
-- statement:
--   The short-note cap turns displayed polynomial degree, coefficient height, nonvanishing, and quadratic logarithmic-rate hypotheses into an irrationality bound for a fixed real target function. The submitted module contains the source declarations pairWidth, pairHeight, polynomialRemainder, CapHypotheses, coeffL1_nonneg, among others. Source topic: Quadratic short-note irrationality cap.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/PaperShortCapR9.lean#L20-L181
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
The complete short-note cap, as an compiled proof-source candidate.

This is not an additional source-supply axiom: the hypotheses are the displayed
polynomial degree, l1 height, nonvanishing and logarithmic-rate hypotheses.
`QuadUpper` makes the paper's upper o(n^2) inequalities precise. The result is
proved for any real target function, hence also for the actual paperLambert.
No condition uniform in x beyond common constants is required: each fixed x
has its own eventual estimates, exactly as in the paper.

The long-record max-coefficient-height and limsup conclusions are separate.
-/
namespace ErdosProblems.Erdos1049.PaperR9
open Filter Asymptotics
open scoped Topology

noncomputable def pairWidth (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ :=
  max (U n).natDegree (V n).natDegree



noncomputable def polynomialRemainder (U V : ℕ → Polynomial ℤ)
    (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x -
    (V n).eval₂ (Int.castRingHom ℝ) x

















end ErdosProblems.Erdos1049.PaperR9


