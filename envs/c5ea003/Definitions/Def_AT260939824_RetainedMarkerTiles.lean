-- Prove2me | Definitions.Def_AT260939824_RetainedMarkerTiles
-- name    : AT260939824_RetainedMarkerTiles
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:52:36.386064+00:00
-- url     : https://prove2.me/theorems/3735a460-94db-42d3-bb7e-5695665e0ec8
-- title:
--   Elementary marker-box subdivisions and retained rectangles
-- statement:
--   For continuous marker-box data $B$ over an anisotropic clopen marker set $M$ in a $\mathbb Z^d$-space, the box at center $a$ has the integer lower and upper cuts supplied by $B$. In coordinate $i$, collect both cuts of every orbit marker within six coordinate scales of $a$ into a finite level set. A grid cell uses consecutive levels in each coordinate and is contained in its parent box. Such a cell $R$ is retained when
--   $$a\cdot x\in M,\qquad
--   \operatorname{relint}R\cap B_b=\varnothing
--   \quad\text{for every marker }b\text{ of smaller priority than }a.$$
--   The retained-tile family consists of rectangles retained for some parent. With positive scales these rectangles cover real orbit coordinates; when the priority radius is at least six, their full-dimensional interiors are disjoint. Their closed-box containment properties also handle subdivision boundaries.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RetainedMarkerTiles.lean, selected declaration lines 22-29, 31-33, 35-39, 41-48, 50-53, 55-58, 60-66, 68-74, 76-92, 94-103, 105-130, 132-136, 138-139, 141-157, 159-190; SHA-256 d1fc3bdb38c8798c50a3eebac394f29c1b01964083fc46ff2152143790a16267. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
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
import Definitions.Def_AT260939824_RectangularCells
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

/-!
# Actual retained marker-box subdivisions

Each marker box is subdivided at the finite cut levels of all markers
within six scales. Only the elementary boxes inside the parent are used.
The retained boxes avoid every lower-priority containing marker box.
These literal integer rectangles cover real orbit coordinates and have
pairwise disjoint full-dimensional interiors.
-/

namespace AbelianTargets
noncomputable section

variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
variable {M : AnisotropicClopenMarkers d L X} {S : ℕ}

def ContinuousMarkerBoxes.markerBox (B : ContinuousMarkerBoxes M S) (x : X)
    (a : Lattice d) : RectangularCell d where
  lower i := (B.cuts x a i).1
  upper i := (B.cuts x a i).2
  ordered i := by
    have h := B.cuts_bounds x a i
    have hL : (0 : ℤ) ≤ L i := by positivity
    omega

def ContinuousMarkerBoxes.localCutLevels (B : ContinuousMarkerBoxes M S) (x : X)
    (a : Lattice d) (i : Fin d) : Finset ℤ :=
  (inactiveOrbitNeighbors M 6 x a).biUnion (fun b => {(B.cuts x b i).1,(B.cuts x b i).2})

theorem ContinuousMarkerBoxes.mem_selfNeighborhood (B : ContinuousMarkerBoxes M S)
    (x : X) (a : Lattice d) (ha : a +ᵥ x ∈ M.markers) :
    a ∈ inactiveOrbitNeighbors M 6 x a := by
  apply (mem_inactiveOrbitNeighbors_of_mem M 6 x a a ha).mpr
  exact ⟨ha,by intro i; simp⟩

theorem ContinuousMarkerBoxes.self_cuts_mem_levels (B : ContinuousMarkerBoxes M S)
    (x : X) (a : Lattice d) (ha : a +ᵥ x ∈ M.markers) (i : Fin d) :
    (B.cuts x a i).1 ∈ B.localCutLevels x a i ∧
      (B.cuts x a i).2 ∈ B.localCutLevels x a i := by
  classical
  constructor
  · exact Finset.mem_biUnion.mpr ⟨a,B.mem_selfNeighborhood x a ha,by simp⟩
  · exact Finset.mem_biUnion.mpr ⟨a,B.mem_selfNeighborhood x a ha,by simp⟩

def ContinuousMarkerBoxes.GridCell (B : ContinuousMarkerBoxes M S) (x : X)
    (a : Lattice d) (R : RectangularCell d) : Prop :=
  ∀ i,(R.lower i,R.upper i) ∈ consecutivePairs (B.localCutLevels x a i) ∧
    (B.cuts x a i).1 ≤ R.lower i ∧ R.upper i ≤ (B.cuts x a i).2

theorem ContinuousMarkerBoxes.GridCell.positive
    {B : ContinuousMarkerBoxes M S} {x : X} {a : Lattice d} {R : RectangularCell d}
    (hR : B.GridCell x a R) (i : Fin d) : R.lower i < R.upper i :=
  ((mem_consecutivePairs _ _ _).mp (hR i).1).2.2.1

theorem ContinuousMarkerBoxes.GridCell.subset_parent
    {B : ContinuousMarkerBoxes M S} {x : X} {a : Lattice d} {R : RectangularCell d}
    (hR : B.GridCell x a R) : R.closedBox ⊆ (B.markerBox x a).closedBox := by
  intro z hz i
  have hlo : ((B.cuts x a i).1 : ℝ) ≤ (R.lower i : ℝ) := by exact_mod_cast (hR i).2.1
  have hhi : (R.upper i : ℝ) ≤ ((B.cuts x a i).2 : ℝ) := by exact_mod_cast (hR i).2.2
  exact ⟨hlo.trans (hz i).1,(hz i).2.trans hhi⟩

theorem ContinuousMarkerBoxes.markerBox_positive
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (x : X) (a : Lattice d) (i : Fin d) :
    (B.markerBox x a).lower i < (B.markerBox x a).upper i := by
  have h := B.cuts_bounds x a i
  have hi : (1 : ℤ) ≤ L i := by exact_mod_cast hL i
  change (B.cuts x a i).1 < (B.cuts x a i).2
  omega

theorem ContinuousMarkerBoxes.exists_gridCell_cover
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (x : X)
    (a : Lattice d) (ha : a +ᵥ x ∈ M.markers) (z : RealCoordinates d)
    (hz : z ∈ (B.markerBox x a).closedBox) :
    ∃ R : RectangularCell d,B.GridCell x a R ∧ z ∈ R.closedBox := by
  have h : ∀ i,∃ l u,(l,u) ∈ consecutivePairs (B.localCutLevels x a i) ∧
      (B.cuts x a i).1 ≤ l ∧ u ≤ (B.cuts x a i).2 ∧
      (l : ℝ) ≤ z i ∧ z i ≤ (u : ℝ) := by
    intro i
    exact exists_consecutivePair_cover _ _ _ (B.self_cuts_mem_levels x a ha i).1
      (B.self_cuts_mem_levels x a ha i).2 (B.markerBox_positive hL x a i) _ (hz i).1 (hz i).2
  choose l u hp hlo hhi hzlo hzhi using h
  let R : RectangularCell d := {
    lower := l
    upper := u
    ordered := fun i => ((mem_consecutivePairs _ _ _).mp (hp i)).2.2.1.le }
  exact ⟨R,fun i => ⟨hp i,hlo i,hhi i⟩,fun i => ⟨hzlo i,hzhi i⟩⟩

theorem ContinuousMarkerBoxes.parents_near_of_overlap
    (B : ContinuousMarkerBoxes M S) (x : X) {a b : Lattice d}
    (ha : a +ᵥ x ∈ M.markers) (hb : b +ᵥ x ∈ M.markers)
    (hz : ((B.markerBox x a).closedBox ∩ (B.markerBox x b).closedBox).Nonempty) :
    b ∈ inactiveOrbitNeighbors M 6 x a := by
  apply (mem_inactiveOrbitNeighbors_of_mem M 6 x a b ha).mpr
  refine ⟨hb,?_⟩
  have h := (B.rectangularCuts x).overlap_centers (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) hz
  intro i
  simpa only [Nat.cast_mul,Nat.cast_ofNat,abs_sub_comm] using h i

/-- Membership in a competing marker box is constant throughout an
elementary interior. In fact its whole closure is then contained in the
competing box, which also handles points on the grid boundaries. -/
theorem ContinuousMarkerBoxes.GridCell.contained_if_interior_meets
    {B : ContinuousMarkerBoxes M S} {x : X} {a b : Lattice d} {R : RectangularCell d}
    (ha : a +ᵥ x ∈ M.markers) (hb : b +ᵥ x ∈ M.markers)
    (hR : B.GridCell x a R)
    (hz : (R.relativeInterior ∩ (B.markerBox x b).closedBox).Nonempty) :
    R.closedBox ⊆ (B.markerBox x b).closedBox := by
  classical
  obtain ⟨z,hzR,hzb⟩ := hz
  have hzparent := hR.subset_parent (R.relativeInterior_subset hzR)
  have hbnear := B.parents_near_of_overlap x ha hb ⟨z,hzparent,hzb⟩
  have hlevels : ∀ i,(B.cuts x b i).1 ∈ B.localCutLevels x a i ∧
      (B.cuts x b i).2 ∈ B.localCutLevels x a i := by
    intro i
    constructor <;> apply Finset.mem_biUnion.mpr <;> exact ⟨b,hbnear,by simp⟩
  intro w hw i
  have hzi := hzR i
  have hne : R.lower i ≠ R.upper i := ne_of_lt (hR.positive i)
  simp only [RectangularCell.relativeInterior,hne,if_false] at hzi
  have hc := consecutivePair_bounds_of_point (hR i).1 (hlevels i).1 (hlevels i).2
    hzi.1 hzi.2 (hzb i).1 (hzb i).2
  have hlo : ((B.cuts x b i).1 : ℝ) ≤ (R.lower i : ℝ) := by exact_mod_cast hc.1
  have hhi : (R.upper i : ℝ) ≤ ((B.cuts x b i).2 : ℝ) := by exact_mod_cast hc.2
  exact ⟨hlo.trans (hw i).1,(hw i).2.trans hhi⟩

def ContinuousMarkerBoxes.Retained (B : ContinuousMarkerBoxes M S) (x : X)
    (a : Lattice d) (R : RectangularCell d) : Prop :=
  a +ᵥ x ∈ M.markers ∧ B.GridCell x a R ∧
    ∀ b,b +ᵥ x ∈ M.markers → (B.priority x b).val < (B.priority x a).val →
      Disjoint R.relativeInterior (B.markerBox x b).closedBox

def ContinuousMarkerBoxes.retainedTiles (B : ContinuousMarkerBoxes M S) (x : X) :
    Set (RectangularCell d) := {R | ∃ a,B.Retained x a R}

theorem ContinuousMarkerBoxes.retainedTiles_cover
    (B : ContinuousMarkerBoxes M S) (hL : ∀ i,1 ≤ L i) (x : X) (z : RealCoordinates d) :
    ∃ R ∈ B.retainedTiles x,z ∈ R.closedBox := by
  classical
  obtain ⟨a,hza⟩ := B.boxes_cover hL x z
  have hex : ∃ n : ℕ,∃ a : Lattice d,a +ᵥ x ∈ M.markers ∧
      z ∈ (B.markerBox x a).closedBox ∧ (B.priority x a).val = n :=
    ⟨_,a.val,a.property,hza,rfl⟩
  obtain ⟨a,ha,hza,hprio⟩ := Nat.find_spec hex
  obtain ⟨R,hR,hzR⟩ := B.exists_gridCell_cover hL x a ha z hza
  refine ⟨R,⟨a,ha,hR,?_⟩,hzR⟩
  intro b hb hpb
  apply Set.disjoint_left.mpr
  intro w hwR hwb
  have hcontain := hR.contained_if_interior_meets ha hb ⟨w,hwR,hwb⟩
  have hmin := Nat.find_min' hex ⟨b,hb,hcontain hzR,rfl⟩
  omega

theorem ContinuousMarkerBoxes.retained_interiors_unique
    (B : ContinuousMarkerBoxes M S) (hS : 6 ≤ S) (x : X)
    {a b : Lattice d} {R T : RectangularCell d}
    (hR : B.Retained x a R) (hT : B.Retained x b T)
    (hz : (R.relativeInterior ∩ T.relativeInterior).Nonempty) : R = T := by
  obtain ⟨z,hzR,hzT⟩ := hz
  have hza := hR.2.1.subset_parent (R.relativeInterior_subset hzR)
  have hzb := hT.2.1.subset_parent (T.relativeInterior_subset hzT)
  have hprio : B.priority x a = B.priority x b := by
    by_contra hne
    have hv : (B.priority x a).val ≠ (B.priority x b).val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hp | hp
    · exact Set.disjoint_left.mp (hT.2.2 a hR.1 hp) hzT hza
    · exact Set.disjoint_left.mp (hR.2.2 b hT.1 hp) hzR hzb
  have hab : a = b := by
    by_contra hne
    have hbnear := B.parents_near_of_overlap x hR.1 hT.1 ⟨z,hza,hzb⟩
    have hclose := ((mem_inactiveOrbitNeighbors_of_mem M 6 x a b hR.1).mp hbnear).2
    apply B.priority_proper x a b hR.1 hT.1 hne _ hprio
    intro i
    exact (hclose i).trans (by exact_mod_cast Nat.mul_le_mul_right (L i) hS)
  subst b
  have hbounds : ∀ i,R.lower i = T.lower i ∧ R.upper i = T.upper i := by
    intro i
    have hr := hzR i
    have ht := hzT i
    simp only [RectangularCell.relativeInterior,ne_of_lt (hR.2.1.positive i),
      ne_of_lt (hT.2.1.positive i),if_false] at hr ht
    exact consecutivePairs_disjoint_interiors (hR.2.1 i).1 (hT.2.1 i).1 hr.1 hr.2 ht.1 ht.2
  have hlo : R.lower = T.lower := funext (fun i => (hbounds i).1)
  have hhi : R.upper = T.upper := funext (fun i => (hbounds i).2)
  cases R; cases T; cases hlo; cases hhi; rfl

end
end AbelianTargets


