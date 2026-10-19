-- Prove2me | Definitions.Def_AT260939824_CovariantOrbitCuts
-- name    : AT260939824_CovariantOrbitCuts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:49:47.615221+00:00
-- url     : https://prove2.me/theorems/3901281a-6d97-431b-ac52-f0cf2070c879
-- title:
--   Repointing identities for orbit cut data
-- statement:
--   Let $t\in\mathbb Z^d$ repoint a free lattice action from $x$ to $t\cdot x$. Fixed-index marker neighborhoods, priorities, and earlier-cut sets at index $a$ then correspond to those at $a+t$ for the original point. Coordinate cut pairs transform by subtraction of $t_i$.
--
--   These identities express the exact covariance of the priority-cut construction and supply the translation law needed by the resulting marker boxes.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CovariantOrbitCuts.lean, selected declaration lines 17-29, 31-41, 43-80, 82-109; SHA-256 c4d3efeb2efd9478e22aee5373f7f33428d4916e7a6bcdefeab57248b9b9b15f. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_ContinuousOrbitCuts
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedOrbitPriorityCuts
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Repointing covariance of actual orbit cuts

Changing the orbit origin by `t` changes every lattice coordinate by
`-t`. The neighborhood, priorities, and actual cut iteration respect
this change exactly.
-/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

theorem mem_inactiveOrbitNeighbors_repoint
    (M : AnisotropicClopenMarkers d L X) (S : ℕ) (x : X) (t a b : Lattice d) :
    b ∈ inactiveOrbitNeighbors M S (t +ᵥ x) a ↔
      b+t ∈ inactiveOrbitNeighbors M S x (a+t) := by
  classical
  by_cases ha : (a+t) +ᵥ x ∈ M.markers
  · have ha' : a +ᵥ (t +ᵥ x) ∈ M.markers := by simpa only [add_vadd] using ha
    rw [mem_inactiveOrbitNeighbors_of_mem M S _ _ _ ha',
      mem_inactiveOrbitNeighbors_of_mem M S _ _ _ ha]
    simp only [add_vadd,Pi.add_apply,add_sub_add_right_eq_sub]
  · have ha' : a +ᵥ (t +ᵥ x) ∉ M.markers := by simpa only [add_vadd] using ha
    simp only [inactiveOrbitNeighbors,if_neg ha,if_neg ha',Finset.mem_singleton,
      add_left_inj]

theorem fixedOrbitPriority_repoint
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d))
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (x : X) (t a : Lattice d) :
    (fixedOrbitPriorityNeighborhood M hL S free c hproper (t +ᵥ x)).priority a =
      (fixedOrbitPriorityNeighborhood M hL S free c hproper x).priority (a+t) := by
  change markerPriorityExtension _ _ _ (a +ᵥ (t +ᵥ x)) =
    markerPriorityExtension _ _ _ ((a+t) +ᵥ x)
  rw [add_vadd]

theorem earlierPriorityCuts_repoint
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d))
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (x : X) (t a : Lattice d) (n : ℕ) (i : Fin d)
    (old new : Lattice d → ℤ × ℤ)
    (hold : ∀ b,new b = ((old (b+t)).1-t i,(old (b+t)).2-t i)) :
    earlierPriorityCuts (fixedOrbitPriorityNeighborhood M hL S free c hproper (t +ᵥ x)) new n a =
      translatedCuts (-t i)
        (earlierPriorityCuts (fixedOrbitPriorityNeighborhood M hL S free c hproper x) old n (a+t)) := by
  classical
  ext z
  simp only [earlierPriorityCuts,translatedCuts,Finset.mem_biUnion,Finset.mem_filter,
    Finset.mem_insert,Finset.mem_singleton,Finset.mem_image]
  constructor
  · rintro ⟨b,⟨hb,hp⟩,hz | hz⟩
    · refine ⟨(old (b+t)).1,⟨b+t,⟨?_,?_⟩,Or.inl rfl⟩,?_⟩
      · exact (mem_inactiveOrbitNeighbors_repoint M S x t a b).mp hb
      · simpa only [fixedOrbitPriority_repoint M hL S free c hproper x t b] using hp
      · rw [hold] at hz; dsimp at hz; omega
    · refine ⟨(old (b+t)).2,⟨b+t,⟨?_,?_⟩,Or.inr rfl⟩,?_⟩
      · exact (mem_inactiveOrbitNeighbors_repoint M S x t a b).mp hb
      · simpa only [fixedOrbitPriority_repoint M hL S free c hproper x t b] using hp
      · rw [hold] at hz; dsimp at hz; omega
  · rintro ⟨w,⟨b,⟨hb,hp⟩,hw | hw⟩,hz⟩
    · refine ⟨b-t,⟨?_,?_⟩,Or.inl ?_⟩
      · apply (mem_inactiveOrbitNeighbors_repoint M S x t a (b-t)).mpr
        simpa only [sub_add_cancel] using hb
      · rw [fixedOrbitPriority_repoint M hL S free c hproper x t (b-t),sub_add_cancel]
        exact hp
      · rw [hold,sub_add_cancel]; dsimp; omega
    · refine ⟨b-t,⟨?_,?_⟩,Or.inr ?_⟩
      · apply (mem_inactiveOrbitNeighbors_repoint M S x t a (b-t)).mpr
        simpa only [sub_add_cancel] using hb
      · rw [fixedOrbitPriority_repoint M hL S free c hproper x t (b-t),sub_add_cancel]
        exact hp
      · rw [hold,sub_add_cancel]; dsimp; omega

theorem fixedOrbitCutIteration_repoint
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d))
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (hscale : ∀ i,32*((2*S+1)^d) ≤ L i) (x : X) (t : Lattice d) (i : Fin d) :
    ∀ n a,
      priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper (t +ᵥ x))
        (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) n a =
      ((priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper x)
        (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) n (a+t)).1-t i,
       (priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper x)
        (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) n (a+t)).2-t i) := by
  intro n
  induction n with
  | zero => intro a; simp only [priorityCutIteration,Pi.add_apply]; congr 1 <;> ring
  | succ n ih =>
      intro a
      have he := earlierPriorityCuts_repoint M hL S free c hproper x t a n i _ _ ih
      rw [priorityCutIteration,priorityCutIteration,
        fixedOrbitPriority_repoint M hL S free c hproper x t a]
      split_ifs
      · simp only [he]
        have hlo : a i-3*(L i : ℤ) = ((a+t) i-3*(L i : ℤ))+(-t i) := by simp; ring
        have hhi : a i+2*(L i : ℤ) = ((a+t) i+2*(L i : ℤ))+(-t i) := by simp; ring
        rw [hlo,hhi,selectedCut_translated,selectedCut_translated]
        rfl
      · exact ih a

end
end AbelianTargets


