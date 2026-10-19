-- Prove2me | solution 1 for AbelianTargets.hasContinuousHom_of_probabilityField
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:12:39.148648+00:00
-- url     : https://prove2.me/submissions/ce4bd280-49e1-4369-811c-a61987b97193

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
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
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.Actions
section
/-!
Definitions for arXiv:2609.39824v1, Sections 2.1 and 7.2.
The action convention is `(g +ᵥ x)(u) = x(u + g)`.
-/

namespace AbelianTargets





















theorem hasContinuousHom_of_positive {d : ℕ} {X V : Type*}
    [AddAction (Lattice d) X] [TopologicalSpace X] [TopologicalSpace V]
    {H : SimpleGraph V} (c : X → V) (hc : Continuous c)
    (he : ∀ x (i : Fin d), H.Adj (c x) (c (unitVector i +ᵥ x))) :
    HasContinuousHom (d := d) (X := X) H := by
  refine ⟨c, hc, ?_⟩
  rintro x y ⟨i, h | h⟩
  · simpa [h] using he x i
  · simpa [h] using (he y i).symm

























end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.Probability
section
/-!
# Probability coordinates and exact graph rounding

This file formalizes the numerical part of the proof of Theorem 1.4 in
arXiv:2609.39824, Section 6. It does not assume existence of the geometric
approximate parity field used earlier in that proof.
-/

open scoped BigOperators

namespace AbelianTargets



namespace Probability

variable {V : Type*} [Fintype V]



















theorem chooseMax_bound [Nonempty V] (p : Probability V) :
    1 / (Fintype.card V : ℝ) ≤ p.mass (chooseMax p) :=
  (Classical.choose_spec p.exists_max_mass).2

theorem chooseMax_pos [Nonempty V] (p : Probability V) :
    0 < p.mass (chooseMax p) := by
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
  exact (one_div_pos.mpr hcard).trans_le p.chooseMax_bound



end Probability

variable {V : Type*} [Fintype V]



/-- The precise rounding implication in Section 6: an approximation with error
less than `1 / (2 * |V|)` gives an exact graph edge between maximum-mass choices. -/
theorem rounding_edge [Nonempty V] (H : SimpleGraph V)
    (p q p' : Probability V) (hcompat : Compatible H p q)
    (hclose : ∀ v,
      |p'.mass v - q.mass v| < 1 / (2 * (Fintype.card V : ℝ))) :
    H.Adj (Probability.chooseMax p) (Probability.chooseMax p') := by
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
  have hhalf : 1 / (2 * (Fintype.card V : ℝ)) <
      1 / (Fintype.card V : ℝ) :=
    one_div_lt_one_div_of_lt hcard (by linarith)
  have hdiff := (abs_lt.mp (hclose (Probability.chooseMax p'))).2
  have hmass := p'.chooseMax_bound
  have hq : 0 < q.mass (Probability.chooseMax p') := by linarith
  exact hcompat _ _ p.chooseMax_pos hq

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.Rounding
section
/-!
# Continuous finite-range rounding

The final step of Theorem 1.4 and Proposition 7.1 is proved here.
The existence of `ProbabilityField` is a separate, unproved geometric
obligation, never an axiom of this project.
-/

namespace AbelianTargets

/-- Any selection from the finite image of a continuous map into a T1 space
is continuous. This justifies a fixed maximum-mass selection even at ties. -/
theorem continuous_comp_of_finite_range
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    [TopologicalSpace Z] {f : X → Y} (hf : Continuous f)
    (hfinite : (Set.range f).Finite) (g : Y → Z) :
    Continuous (fun x => g (f x)) := by
  letI : Finite (Set.range f) := hfinite.to_subtype
  haveI : DiscreteTopology (Set.range f) := inferInstance
  exact (continuous_of_discreteTopology (f := fun y : Set.range f => g y.val)).comp
    hf.rangeFactorization





end AbelianTargets

end

/-!
# Continuous finite-range rounding

The final step of Theorem 1.4 and Proposition 7.1 is proved here.
The existence of `ProbabilityField` is a separate, unproved geometric
obligation, never an axiom of this project.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets

theorem solution
    {d : ℕ} {X V : Type*} [AddAction (Lattice d) X]
    [TopologicalSpace X] [TopologicalSpace V] [Fintype V]
    {H : SimpleGraph V} (field : ProbabilityField (d := d) (X := X) H) :
    HasContinuousHom (d := d) (X := X) H := by
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    letI : Nonempty V := (field.p (Classical.choice hX)).nonempty
    let c : X → V := fun x => Probability.chooseMax (field.p x)
    have hc : Continuous c := continuous_comp_of_finite_range
      field.continuous_p field.finite_range_p Probability.chooseMax
    apply hasContinuousHom_of_positive c hc
    intro x i
    exact rounding_edge H (field.p x) (field.q x)
      (field.p (unitVector i +ᵥ x)) (field.compatible x) (field.close x i)
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    refine ⟨isEmptyElim, continuous_iff_continuousAt.mpr (fun x => isEmptyElim x), ?_⟩
    intro x
    exact isEmptyElim x
