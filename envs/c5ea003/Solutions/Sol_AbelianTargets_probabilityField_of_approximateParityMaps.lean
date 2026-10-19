-- Prove2me | solution 1 for AbelianTargets.probabilityField_of_approximateParityMaps
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:13:41.73216+00:00
-- url     : https://prove2.me/submissions/f5c82ed4-aaa6-46a4-b8e6-020199077599

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# The analytic implication in Section 6

This file checks composition with an equivariant support model, choice of
a uniform error on a compact source, and exact graph rounding.
The actual presentation complex is constructed in separate modules;
existence of its approximate parity maps remains an explicit geometric input.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets

theorem solution
    {d : ℕ} {X Y V : Type*} [TopologicalSpace X]
    [AddAction (Lattice d) X] [MetricSpace Y] [CompactSpace Y]
    [Fintype V] [Nonempty V] {H : SimpleGraph V} {τ : Y → Y}
    (model : SupportModel H τ)
    (approx : ApproximateParityMaps (d := d) X Y τ) :
    Nonempty (ProbabilityField (d := d) (X := X) H) := by
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
  have hε : 0 < 1 / (2 * (Fintype.card V : ℝ)) := by positivity
  have huc : UniformContinuous (fun y => (model.p y).mass) :=
    CompactSpace.uniformContinuous_of_continuous
      (Probability.continuous_mass.comp model.continuous_p)
  obtain ⟨δ, hδ, hbound⟩ :=
    Metric.uniformContinuous_iff.mp huc (1 / (2 * (Fintype.card V : ℝ))) hε
  obtain ⟨f, hf, hfinite, he⟩ := approx δ hδ
  refine ⟨{
    p := fun x => model.p (f x)
    q := fun x => model.q (f x)
    continuous_p := model.continuous_p.comp hf
    finite_range_p := ?_
    compatible := fun x => model.compatible (f x)
    close := ?_ }⟩
  · apply (hfinite.image model.p).subset
    rintro z ⟨x, rfl⟩
    exact ⟨f x, ⟨x, rfl⟩, rfl⟩
  · intro x i v
    have hclose := (dist_pi_lt_iff hε).mp (hbound (he x i)) v
    simpa only [Real.dist_eq, model.first_swap] using hclose
