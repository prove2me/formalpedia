-- Prove2me | Definitions.Def_AT260939824_ContinuousOrbitCuts
-- name    : AT260939824_ContinuousOrbitCuts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:47:04.577712+00:00
-- url     : https://prove2.me/theorems/10eb69ec-6218-49b9-a17e-471c6487f49a
-- title:
--   Continuous finite data on fixed orbit indices
-- statement:
--   Let $M$ be a clopen marker set for a lattice action and let $g\in\mathbb Z^d$ be a fixed index. Marker membership is represented by a Boolean flag, and a continuous marker priority is extended by a default value outside $M$. The finite neighbor list is the set of nearby marker indices when $g$ is active, and the singleton $\{g\}$ otherwise.
--
--   With discrete topologies on the finite data, these definitions and continuity interfaces support parameter-dependent cut selection.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/ContinuousOrbitCuts.lean, selected declaration lines 8-11, 13-45, 47-49, 51-55, 60-62, 64-68, 70-93, 95-100, 102-121; SHA-256 b71d95fdfbc4a2914c2c431a1666e542dddf9a51915c720475ce3466ee3cb415. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_ContinuousPriorityCuts
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_Dimension
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

namespace AbelianTargets
noncomputable section
open Filter Topology

def markerPriorityExtension {X V : Type*} [TopologicalSpace X]
    (A : Set X) (c : A → V) (v : V) (x : X) : V := by
  classical
  exact if hx : x ∈ A then c ⟨x,hx⟩ else v

theorem continuous_markerPriorityExtension {X V : Type*}
    [TopologicalSpace X] [TopologicalSpace V] (A : Set X)
    (hA : IsClopen A) (c : A → V) (hc : Continuous c) (v : V) :
    Continuous (markerPriorityExtension A c v) := by
  classical
  apply continuous_def.mpr
  intro U hU
  have heq : markerPriorityExtension A c v ⁻¹' U =
      Subtype.val '' (c ⁻¹' U) ∪ (if v ∈ U then Aᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ A
    · simp only [Set.mem_preimage,markerPriorityExtension,dif_pos hx,Set.mem_union,
        Set.mem_image]
      constructor
      · intro h
        exact Or.inl ⟨⟨x,hx⟩,h,rfl⟩
      · rintro (⟨a,ha,he⟩ | h)
        · subst x; exact ha
        · split_ifs at h <;> simp_all
    · simp only [Set.mem_preimage,markerPriorityExtension,dif_neg hx,Set.mem_union,
        Set.mem_image]
      constructor
      · intro h; right; simp [h,hx]
      · rintro (⟨a,ha,he⟩ | h)
        · exact (hx (he ▸ a.property)).elim
        · split_ifs at h with hv
          · exact hv
          · exact (Set.notMem_empty x h).elim
  rw [heq]
  apply (hA.isOpen.isOpenMap_subtype_val _ (hc.isOpen_preimage U hU)).union
  split_ifs
  · exact hA.compl.isOpen
  · exact isOpen_empty

def markerFlag {X : Type*} [TopologicalSpace X] (A : Set X) (x : X) : Bool := by
  classical
  exact if x ∈ A then true else false

theorem continuous_markerFlag {X : Type*} [TopologicalSpace X]
    (A : Set X) (hA : IsClopen A) : Continuous (markerFlag A) := by
  classical
  have h := continuous_markerPriorityExtension A hA (fun _ => true) continuous_const false
  simpa [markerPriorityExtension,markerFlag] using h

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]

def orbitCandidateBox (S : ℕ) (L : Fin d → ℕ) (g : Lattice d) : Finset (Lattice d) :=
  (Fintype.piFinset (fun i => Finset.Icc (-(S : ℤ)*(L i : ℤ)) ((S : ℤ)*(L i : ℤ)))).image
    (fun h => h+g)

def inactiveOrbitNeighbors (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (x : X) (g : Lattice d) : Finset (Lattice d) := by
  classical
  exact if g +ᵥ x ∈ M.markers then
    (orbitCandidateBox S L g).filter (fun h => h +ᵥ x ∈ M.markers) else {g}

/-- The actual finite neighbor lists on a fixed lattice index vary
continuously. Inactive indices have only their self-neighbor. -/
theorem continuous_inactiveOrbitNeighbors
    (M : AnisotropicClopenMarkers d L X) (S : ℕ) (g : Lattice d)
    [TopologicalSpace (Finset (Lattice d))] [DiscreteTopology (Finset (Lattice d))] :
    Continuous (fun x => inactiveOrbitNeighbors M S x g) := by
  classical
  let B := orbitCandidateBox S L g
  let mask (x : X) : B → Bool := fun h => markerFlag M.markers (h.val +ᵥ x)
  have hm : Continuous mask := continuous_pi (fun h =>
    (continuous_markerFlag M.markers M.clopen).comp (continuous_const_vadd h.val))
  have hg : Continuous (fun x => markerFlag M.markers (g +ᵥ x)) :=
    (continuous_markerFlag M.markers M.clopen).comp (continuous_const_vadd g)
  let output (u : Bool × (B → Bool)) : Finset (Lattice d) :=
    if u.1 then B.attach.filter (fun h => u.2 h = true) |>.image Subtype.val else {g}
  have ho : Continuous output := continuous_of_discreteTopology
  convert ho.comp (hg.prodMk hm) using 1
  funext x
  dsimp [output,mask,inactiveOrbitNeighbors]
  by_cases hx : g +ᵥ x ∈ M.markers
  · simp only [markerFlag,if_pos hx,if_true]
    ext h
    simp [B,and_comm]
  · simp [markerFlag,hx]

theorem continuous_orbitPriorityExtension {P : ℕ}
    (M : AnisotropicClopenMarkers d L X) (c : M.markers → Fin P)
    (hc : Continuous c) (v : Fin P) (g : Lattice d) :
    Continuous (fun x => markerPriorityExtension M.markers c v (g +ᵥ x)) :=
  (continuous_markerPriorityExtension M.markers M.clopen c hc v).comp
    (continuous_const_vadd g)

/-- Once the elementary neighborhood fields are packaged, the actual
fixed-index origin cuts are continuous. The hypotheses specify the exact
neighbor and priority data, rather than assuming continuity of the cuts.
This scratch file does not yet package the neighborhood fields itself. -/
theorem continuous_actualOrbitCuts {P : ℕ}
    [TopologicalSpace (Finset (Lattice d))] [DiscreteTopology (Finset (Lattice d))]
    (M : AnisotropicClopenMarkers d L X) (S : ℕ)
    (c : M.markers → Fin P) (hc : Continuous c) (v : Fin P)
    (N : X → PriorityNeighborhood (Lattice d) P)
    (hnear : ∀ x g,(N x).nearby g = inactiveOrbitNeighbors M S x g)
    (hpriority : ∀ x g,(N x).priority g = markerPriorityExtension M.markers c v (g +ᵥ x))
    (hP : 1 ≤ P) (hL : ∀ i,32*P ≤ L i) (i : Fin d) (n : ℕ) (g : Lattice d) :
    Continuous (fun x => priorityCutIteration (N x) hP (hL i) (fun h => h i) n g) := by
  apply continuous_priorityCutIteration N hP (hL i) (fun _ h => h i)
  · intro h
    simpa only [hnear] using continuous_inactiveOrbitNeighbors M S h
  · intro h
    simpa only [hpriority] using continuous_orbitPriorityExtension M c hc v h
  · intro h
    exact continuous_const



end
end AbelianTargets


