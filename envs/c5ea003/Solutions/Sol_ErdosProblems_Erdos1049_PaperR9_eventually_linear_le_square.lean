-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR9.eventually_linear_le_square
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:15:20.518922+00:00
-- url     : https://prove2.me/submissions/82b9ef82-f178-4ba0-8627-848298f8793c

import Definitions.Def_ErdosProblems_Erdos1049_BezoutPluckerJets
import Definitions.Def_ErdosProblems_Erdos1049_PaperAsymptoticsR9
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
theorem solution (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * (2 * (n : ℝ) + 1) ≤ ε * sqScale n := by
  -- API: Algebra/Order/Archimedean/Basic.lean, `exists_nat_gt`.
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (3 * C / ε))
  apply eventually_atTop.2
  refine ⟨N, ?_⟩
  intro n hn
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans (hN.le.trans hnn)
  have hnc : 3 * C / ε ≤ (n : ℝ) :=
    (le_max_right _ _).trans (hN.le.trans hnn)
  have hmul : 3 * C ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hnc
  have hnn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hprod := mul_le_mul_of_nonneg_right hmul hnn0
  have hlin : C * (2 * (n : ℝ) + 1) ≤ 3 * C * n := by
    nlinarith
  dsimp [sqScale]
  nlinarith
