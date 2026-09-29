-- Prove2me | solution 1 for ZeroFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:57:46.588897+00:00
-- url     : https://prove2.me/submissions/a0a65d92-1bdc-4853-b7cb-4864f57e1215

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix

-- from Zeta23.FromPNTPlus.StrongPNTPrefix
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (sorry-free prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory










open Classical












open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical

theorem solution {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by
  have zero_mem_closedBall : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero, norm_zero]
    exact zero_le_one
  have ρ_mem_closedBall : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero]
    linarith[hρ.1]
  have orderAtZeroIsZero : analyticOrderAt f 0 = 0 := by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1 ↦ hf_neq_zero_at_zero a)
  have finiteOrder : analyticOrderAt f ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfAnalytic (Metric.isPreconnected_closedBall) zero_mem_closedBall ρ_mem_closedBall (lt_top_iff_ne_top.mp ?_)
    rw[orderAtZeroIsZero]
    exact ENat.top_pos
  have AnalyticAt_ρ : AnalyticAt ℂ f ρ := by exact (hfAnalytic ρ ρ_mem_closedBall)
  obtain ⟨h_ρ, h_ρ_neq_zero_at_zero, f_eq⟩ := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose_spec
  set g := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose
  refine ⟨g, h_ρ, h_ρ_neq_zero_at_zero, ?_, f_eq⟩
  simp only [ZeroFactor, AnalyticAt_ρ, ↓reduceDIte, ne_eq, finiteOrder, not_false_eq_true,
    smul_eq_mul, g]
