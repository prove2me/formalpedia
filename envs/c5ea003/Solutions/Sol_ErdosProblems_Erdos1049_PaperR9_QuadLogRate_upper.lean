-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR9.QuadLogRate.upper
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:16:01.524707+00:00
-- url     : https://prove2.me/submissions/670c2395-6800-4f73-903a-bd5d0bde6789

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR9_littleO_bound
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
end ErdosProblems.Erdos1049.PaperR9

open Filter Asymptotics
open scoped Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR9 in
theorem solution {f : ℕ → ℝ} {a : ℝ} (hf : QuadLogRate f a) :
    QuadUpper (fun n => Real.log |f n|) a := by
  intro ε hε
  filter_upwards [littleO_bound _ hf ε hε] with n hn
  have h := (le_abs_self (Real.log |f n| - a * sqScale n)).trans hn
  linarith
