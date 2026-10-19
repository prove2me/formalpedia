-- Prove2me | Definitions.Def_AT260939824_MarkerAtlasSideBounds
-- name    : AT260939824_MarkerAtlasSideBounds
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:55:10.287604+00:00
-- url     : https://prove2.me/theorems/1fb7ff9b-1121-42b9-846e-8cd879667317
-- title:
--   Uniform side bounds for actual atlas cells
-- statement:
--   In the marker-box atlas, each endpoint of an active cell side is owned by a marker lying within a bounded multiple of the coordinate scales of an incident parent. The endpoint-owner comparisons bring pairs of cuts into the radius where priority-cut separation applies. Their consequences give the asserted uniform lower and upper side bounds for nondegenerate actual atlas cells.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/MarkerAtlasSideBounds.lean, selected declaration lines 13-30, 32-46, 48-82, 84-100, 102-134; SHA-256 a5e8701e9ff4e861a65c4f418329120173b198ccee8e1836b92c3130224571a7. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualMarkerAtlas
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ContinuousOrbitCuts
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedOrbitPriorityCuts
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RetainedMarkerTiles
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
import Mathlib.Data.Finset.Prod
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
import Mathlib.Tactic
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
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-! Every nondegenerate side of an actual atlas cell is uniformly long.
Endpoint owners lie within twelve scales of one incident parent, so the
checked priority-cut separation applies at radius twenty-four. -/

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

theorem ContinuousMarkerBoxes.GridCell.endpoint_owner
    {B : ContinuousMarkerBoxes M S} {x : X} {a : Lattice d} {R : RectangularCell d}
    (ha : a +ᵥ x ∈ M.markers) (hR : B.GridCell x a R) (i : Fin d) (s : Bool) :
    ∃ b : Lattice d,b +ᵥ x ∈ M.markers ∧
      (∀ j,|b j-a j| ≤ (6*L j : ℕ)) ∧
      ∃ t : Bool,cutSide (R.lower i,R.upper i) s = cutSide (B.cuts x b i) t := by
  have hm : cutSide (R.lower i,R.upper i) s ∈ B.localCutLevels x a i := by
    have hp := (mem_consecutivePairs _ _ _).mp (hR i).1
    cases s <;> simp only [cutSide,Bool.false_eq_true,if_false,if_true]
    · exact hp.1
    · exact hp.2.1
  obtain ⟨b,hb,he⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨hbmark,hclose⟩ := (mem_inactiveOrbitNeighbors_of_mem M 6 x a b ha).mp hb
  refine ⟨b,hbmark,hclose,?_⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with he | he
  · exact ⟨false,by simpa only [cutSide,Bool.false_eq_true,if_false] using he⟩
  · exact ⟨true,by simpa only [cutSide,if_true] using he⟩

theorem ContinuousMarkerBoxes.GridCell.face_endpoint_owner
    {B : ContinuousMarkerBoxes M S} {x : X} {a : Lattice d} {R : RectangularCell d}
    (ha : a +ᵥ x ∈ M.markers) (hR : B.GridCell x a R)
    (z : RealCoordinates d) (i : Fin d) (s : Bool) :
    ∃ b : Lattice d,b +ᵥ x ∈ M.markers ∧
      (∀ j,|b j-a j| ≤ (6*L j : ℕ)) ∧
      ∃ t : Bool,cutSide ((R.faceAt z).lower i,(R.faceAt z).upper i) s =
        cutSide (B.cuts x b i) t := by
  cases s
  · by_cases he : z i = (R.upper i : ℝ)
    · simpa [cutSide,RectangularCell.faceAt,he] using hR.endpoint_owner ha i true
    · simpa [cutSide,RectangularCell.faceAt,he] using hR.endpoint_owner ha i false
  · by_cases he : z i = (R.lower i : ℝ)
    · simpa [cutSide,RectangularCell.faceAt,he] using hR.endpoint_owner ha i false
    · simpa [cutSide,RectangularCell.faceAt,he] using hR.endpoint_owner ha i true

theorem ContinuousMarkerBoxes.pointCell_endpoint_owner
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 6 ≤ S) (x : X)
    (z : RealCoordinates d) {a : Lattice d}
    (ha : a +ᵥ x ∈ M.markers) (hza : z ∈ (B.markerBox x a).closedBox)
    (i : Fin d) (s : Bool) :
    ∃ b : Lattice d,b +ᵥ x ∈ M.markers ∧
      (∀ j,|b j-a j| ≤ (12*L j : ℕ)) ∧
      ∃ t : Bool,cutSide (((B.tiling hL hS x).pointCell z).lower i,
        ((B.tiling hL hS x).pointCell z).upper i) s = cutSide (B.cuts x b i) t := by
  let T := B.tiling hL hS x
  have hex : ∃ R ∈ T.incidentFinset z,
      cutSide ((T.pointCell z).lower i,(T.pointCell z).upper i) s =
        cutSide ((R.faceAt z).lower i,(R.faceAt z).upper i) s := by
    cases s
    · obtain ⟨R,hR,he⟩ := (T.incidentFinset z).exists_mem_eq_sup'
        (T.incidentFinset_nonempty z) (fun R => (R.faceAt z).lower i)
      exact ⟨R,hR,he⟩
    · obtain ⟨R,hR,he⟩ := (T.incidentFinset z).exists_mem_eq_inf'
        (T.incidentFinset_nonempty z) (fun R => (R.faceAt z).upper i)
      exact ⟨R,hR,he⟩
  obtain ⟨R,hR,he⟩ := hex
  obtain ⟨⟨c,hc,hgrid,hkeep⟩,hzR⟩ := (T.mem_incidentFinset z R).mp hR
  have hzc := hgrid.subset_parent hzR
  have hcnear := B.parents_near_of_overlap x ha hc ⟨z,hza,hzc⟩
  have hcclose := ((mem_inactiveOrbitNeighbors_of_mem M 6 x a c ha).mp hcnear).2
  obtain ⟨b,hb,hbc,t,het⟩ := hgrid.face_endpoint_owner hc z i s
  refine ⟨b,hb,?_,t,he.trans het⟩
  intro j
  have hbabs := abs_add_le (b j-c j) (c j-a j)
  have hb := hbc j
  have hc := hcclose j
  have hid : b j-c j+(c j-a j) = b j-a j := by ring
  rw [hid] at hbabs
  push_cast at hb hc ⊢
  omega

theorem ContinuousMarkerBoxes.cutSide_same_owner_separated
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (x : X) (a : Lattice d)
    (i : Fin d) (s t : Bool)
    (hne : cutSide (B.cuts x a i) s ≠ cutSide (B.cuts x a i) t) :
    ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) <
      |cutSide (B.cuts x a i) s-cutSide (B.cuts x a i) t| := by
  have hdiv : ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) ≤ (L i : ℤ) :=
    by exact_mod_cast Nat.div_le_self (L i) (16*((2*S+1)^d))
  have hb := B.cuts_bounds x a i
  have hli : (1 : ℤ) ≤ L i := by exact_mod_cast hL i
  cases s <;> cases t <;> simp only [cutSide,Bool.false_eq_true,if_false,if_true] at hne ⊢
  · exact (hne rfl).elim
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega
  · exact (hne rfl).elim

theorem ContinuousMarkerBoxes.atlas_side_bounds
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (hS : 24 ≤ S) (x : X)
    {R : RectangularCell d} (hR : R ∈ B.atlasCells hL (by omega) x)
    (i : Fin d) (hi : R.lower i < R.upper i) :
    ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) < R.upper i-R.lower i ∧
      R.upper i-R.lower i ≤ (6*L i : ℕ) := by
  obtain ⟨z,rfl⟩ := hR
  obtain ⟨a,hza⟩ := B.boxes_cover hL x z
  obtain ⟨b,hb,hba,s,he₁⟩ := B.pointCell_endpoint_owner hL (by omega) x z a.property hza i false
  obtain ⟨c,hc,hca,t,he₂⟩ := B.pointCell_endpoint_owner hL (by omega) x z a.property hza i true
  have hsep : ((L i/(16*((2*S+1)^d)) : ℕ) : ℤ) <
      |cutSide (B.cuts x b i) s-cutSide (B.cuts x c i) t| := by
    by_cases he : b = c
    · subst c
      apply B.cutSide_same_owner_separated hL x b i s t
      intro he
      simp only [cutSide,Bool.false_eq_true,if_false,if_true] at he₁ he₂
      unfold cutSide at he
      rw [← he₁,← he₂] at he
      exact (ne_of_lt hi) he
    · apply B.cuts_separated x b c hb hc he
      intro j
      have hh := abs_sub_le (c j) (a.val j) (b j)
      have hb := hba j
      have hc := hca j
      rw [abs_sub_comm (a.val j) (b j)] at hh
      have hs : (24*L j : ℕ) ≤ S*L j := Nat.mul_le_mul_right _ hS
      push_cast at hb hc hs ⊢
      omega
  simp only [cutSide,Bool.false_eq_true,if_false,if_true] at he₁ he₂
  unfold cutSide at hsep
  rw [← he₁,← he₂,abs_sub_comm,abs_of_nonneg (by omega)] at hsep
  exact ⟨hsep,(B.tiling hL (by omega) x).cells_bounded ⟨z,rfl⟩ i⟩

end
end AbelianTargets


