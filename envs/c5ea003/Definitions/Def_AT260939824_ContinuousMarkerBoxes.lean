-- Prove2me | Definitions.Def_AT260939824_ContinuousMarkerBoxes
-- name    : AT260939824_ContinuousMarkerBoxes
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:50:56.340131+00:00
-- url     : https://prove2.me/theorems/5c32e26b-175f-434a-a984-4963455b9400
-- title:
--   Continuous equivariant marker priorities and cuts
-- statement:
--   For a lattice action, marker scales $L_i$, and neighborhood parameter $S$, continuous marker-box data consist of finite priorities in $\{0,\ldots,(2S+1)^d-1\}$ and integer lower and upper cuts. Priorities distinguish nearby markers, cuts satisfy the prescribed coordinate windows and separation bounds, and both vary continuously with the action point. Repointing by $t$ shifts indices by $t$ and subtracts $t_i$ from coordinate cuts.
--
--   The record supplies the concrete covariant input for retained rectangular tilings.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/ContinuousMarkerBoxes.lean, selected declaration lines 17-33, 35-42, 44-48, 50-72; SHA-256 cb291327974c425612919e90d31318bc54c76ea9341cda54b88a6686cbfa9ced. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_ContinuousOrbitCuts
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_CovariantOrbitCuts
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
# Actual continuous covariant marker boxes

This record contains cut data, rather than a tiling or an assumed atlas.
Its existence follows from the checked finite-priority construction on
the actual marker graph. It supplies all inputs to retained subdivisions.
-/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

structure ContinuousMarkerBoxes (M : AnisotropicClopenMarkers d L X) (S : ℕ) where
  priority : X → Lattice d → Fin ((2*S+1)^d)
  priority_continuous : ∀ a,Continuous (fun x => priority x a)
  priority_repoint : ∀ x t a,priority (t +ᵥ x) a = priority x (a+t)
  priority_proper : ∀ (x : X) (a b : Lattice d),a +ᵥ x ∈ M.markers → b +ᵥ x ∈ M.markers → a ≠ b →
    (∀ i,|b i-a i| ≤ (S*L i : ℕ)) → priority x a ≠ priority x b
  cuts : X → Lattice d → Fin d → ℤ × ℤ
  cuts_continuous : ∀ a i,Continuous (fun x => cuts x a i)
  cuts_bounds : ∀ x a i,a i-3*(L i : ℤ) ≤ (cuts x a i).1 ∧
    (cuts x a i).1 ≤ a i-2*(L i : ℤ) ∧
    a i+2*(L i : ℤ) ≤ (cuts x a i).2 ∧ (cuts x a i).2 ≤ a i+3*(L i : ℤ)
  cuts_repoint : ∀ x t a i,cuts (t +ᵥ x) a i =
    ((cuts x (a+t) i).1-t i,(cuts x (a+t) i).2-t i)
  cuts_separated : ∀ (x : X) (a b : Lattice d),a +ᵥ x ∈ M.markers → b +ᵥ x ∈ M.markers → a ≠ b →
    (∀ j,|b j-a j| ≤ (S*L j : ℕ)) → ∀ i s t,
      ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) <
        |cutSide (cuts x a i) s-cutSide (cuts x b i) t|

def ContinuousMarkerBoxes.rectangularCuts
    {M : AnisotropicClopenMarkers d L X} {S : ℕ}
    (B : ContinuousMarkerBoxes M S) (x : X) :
    RectangularCuts L {a : Lattice d | a +ᵥ x ∈ M.markers} where
  lower a i := (B.cuts x a.val i).1
  upper a i := (B.cuts x a.val i).2
  lower_bound a i := ⟨(B.cuts_bounds x a.val i).1,(B.cuts_bounds x a.val i).2.1⟩
  upper_bound a i := ⟨(B.cuts_bounds x a.val i).2.2.1,(B.cuts_bounds x a.val i).2.2.2⟩

theorem ContinuousMarkerBoxes.boxes_cover
    {M : AnisotropicClopenMarkers d L X} {S : ℕ}
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (x : X) :
    ∀ z : RealCoordinates d,∃ a,z ∈ (B.rectangularCuts x).box a :=
  anisotropic_marker_boxes_cover M hL x (B.rectangularCuts x)

def markerBoxesFromPriorities
    (M : AnisotropicClopenMarkers d L X) (hL : ∀ i,1 ≤ L i) (S : ℕ)
    (free : IsFree (G := Lattice d) (X := X))
    (c : M.markers → Fin ((2*S+1)^d)) (hc : Continuous c)
    (hproper : ∀ u v,(markerProximityGraph M S free).Adj u v → c u ≠ c v)
    (hscale : ∀ i,32*((2*S+1)^d) ≤ L i) : ContinuousMarkerBoxes M S where
  priority x a := (fixedOrbitPriorityNeighborhood M hL S free c hproper x).priority a
  priority_continuous a := continuous_orbitPriorityExtension M c hc _ a
  priority_repoint := fixedOrbitPriority_repoint M hL S free c hproper
  priority_proper x a b ha hb hne hclose := by
    apply (fixedOrbitPriorityNeighborhood M hL S free c hproper x).proper a b _ hne
    exact (mem_inactiveOrbitNeighbors_of_mem M S x a b ha).mpr ⟨hb,hclose⟩
  cuts x a i := priorityCutIteration (fixedOrbitPriorityNeighborhood M hL S free c hproper x)
    (Nat.one_le_pow _ _ (by omega)) (hscale i) (fun g => g i) ((2*S+1)^d) a
  cuts_continuous a i := by
    letI : TopologicalSpace (Finset (Lattice d)) := ⊥
    letI : DiscreteTopology (Finset (Lattice d)) := ⟨rfl⟩
    exact continuous_fixedOrbitCuts M hL S free c hc hproper hscale i ((2*S+1)^d) a
  cuts_bounds x a i := priorityCutIteration_bounds _ _ _ _ _ _
  cuts_repoint x t a i := fixedOrbitCutIteration_repoint M hL S free c hproper hscale x t i _ a
  cuts_separated x a b ha hb hne hclose i s t := by
    apply priorityCuts_separated _ _ _ _ _ hne s t
    exact (mem_inactiveOrbitNeighbors_of_mem M S x a b ha).mpr ⟨hb,hclose⟩



end
end AbelianTargets


