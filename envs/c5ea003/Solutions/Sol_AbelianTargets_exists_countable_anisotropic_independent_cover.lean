-- Prove2me | solution 1 for AbelianTargets.exists_countable_anisotropic_independent_cover
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:12:05.444168+00:00
-- url     : https://prove2.me/submissions/e9112ba2-6d58-47e5-a265-1e6ce2400454

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite
import Theorems.Thm_AbelianTargets_exists_clopen_shift_independent

set_option autoImplicit false

/-!
# Clopen markers at independent coordinate scales

The initial marker construction in Lemma 3.2 is proved for an actual free
continuous action. Each coordinate has its own scale. This is the input
to the later packing, priority, cut, and rectangular subdivision steps.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable [T1Space X] [SecondCountableTopology X]

theorem solution (L : Fin d → ℕ)
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X)) :
    ∃ C : ℕ → Set X, (∀ n,IsClopen (C n)) ∧
      (∀ n,GraphIndependent (anisotropicDisplacementGraph L free) (C n)) ∧
      ∀ x,∃ n,x ∈ C n := by
  classical
  have hlocal : ∀ x : X, ∃ U : Set X, IsClopen U ∧ x ∈ U ∧
      GraphIndependent (anisotropicDisplacementGraph L free) U := by
    intro x
    let I := {g : Lattice d // g ∈ anisotropicDisplacements L}
    have hs : ∀ g : I, ∃ U : Set X,IsClopen U ∧ x ∈ U ∧
        ∀ y ∈ U,g.val +ᵥ y ∉ U := by
      intro g
      exact exists_clopen_shift_independent zeroDim free x g.val
        ((mem_anisotropicDisplacements L g.val).mp g.property).2
    choose U hclopen hx hshift using hs
    refine ⟨⋂ g : I,U g,isClopen_iInter_of_finite hclopen,Set.mem_iInter.mpr hx,?_⟩
    intro y hy z hz hadj
    obtain ⟨g,hg,hgyz⟩ := hadj
    exact hshift ⟨g,hg⟩ y (Set.mem_iInter.mp hy ⟨g,hg⟩)
      (hgyz.symm ▸ Set.mem_iInter.mp hz ⟨g,hg⟩)
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    choose U hclopen hx hindep using hlocal
    obtain ⟨f,hcov⟩ := isLindelof_univ.indexed_countable_subcover U
      (fun x => (hclopen x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x,hx x⟩)
    exact ⟨fun n => U (f n),fun n => hclopen (f n),fun n => hindep (f n),
      fun x => Set.mem_iUnion.mp (hcov (Set.mem_univ x))⟩
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    exact ⟨fun _ => ∅,fun _ => isClopen_empty,fun _ x => isEmptyElim x,fun x => isEmptyElim x⟩
