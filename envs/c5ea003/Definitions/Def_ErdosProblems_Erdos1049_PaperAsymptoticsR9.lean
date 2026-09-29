-- Prove2me | Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
-- name    : ErdosProblems_Erdos1049_PaperAsymptoticsR9
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T17:45:32.725307+00:00
-- url     : https://prove2.me/theorems/9d2ff170-9894-4c09-bb4c-8ad0cb27428a
-- title:
--   Quadratic asymptotic transfer
-- statement:
--   The lemmas transport little-o quadratic logarithmic rates into exponential bounds and then into integer-form decay and separation. The submitted module contains the source declarations sqScale, QuadUpper, QuadExpUpper, QuadLogRate, sqScale_nonneg, among others. Source topic: Quadratic asymptotic transfer.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos1049/PaperAsymptoticsR9.lean#L25-L262
--   Paper exposition and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1049/erdos-1049-rational-base-lambert.tex#L1252-L1257
--   Correspondence: Erdős #1049 formal source; Zudilin is credited for the relevant rational-base Lambert-series method, without a novelty or all-rational-base claim.

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Prod
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
Quadratic asymptotic transfer, revision of the round-8 return.
Compiled. This file contains proof text, not a kernel receipt.

The asymptotic hypotheses below are estimates, not assumptions of the conclusions.
In particular `cross_product_limits` proves both successor products. The integer
contradiction is the desk's repaired PaperRankTwoCapR7 theorem, reused unchanged.

Pinned API: Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
Filter/metric API: Order/Filter/AtTopBot/Basic.lean and
Topology/MetricSpace/Pseudo/Defs.lean. Exponential/log API:
Analysis/SpecialFunctions/Exp.lean and Log/Basic.lean. Elementary ordered-field
algebra is handled by ring, linarith and explicitly supplied polynomial facts.
-/
namespace ErdosProblems.Erdos1049.PaperR9
open Filter Asymptotics
open scoped Topology

/-- The scale is a real square, avoiding truncated natural subtraction. -/
def sqScale (n : ℕ) : ℝ := (n : ℝ) ^ 2

/-- Upper quadratic rate, with an arbitrary additive epsilon in the rate. -/
def QuadUpper (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ (a + ε) * sqScale n

/-- Upper quadratic exponential rate, allowing zeros of f. -/
def QuadExpUpper (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    |f n| ≤ Real.exp ((a + ε) * sqScale n)

/-- Exact two-sided logarithmic asymptotic; nonvanishing is supplied separately. -/
def QuadLogRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (fun n => Real.log |f n| - a * sqScale n) =o[atTop] sqScale































end ErdosProblems.Erdos1049.PaperR9


