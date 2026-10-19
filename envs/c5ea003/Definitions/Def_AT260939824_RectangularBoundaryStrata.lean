-- Prove2me | Definitions.Def_AT260939824_RectangularBoundaryStrata
-- name    : AT260939824_RectangularBoundaryStrata
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:47:16.931218+00:00
-- url     : https://prove2.me/theorems/6b0c83c3-e26f-41fc-94b8-8290abb3e1c9
-- title:
--   Boundary strata of an integer rectangular tiling
-- statement:
--   An integer rectangular tiling in dimension $d$ with side bounds $K_i\in\mathbb N$ consists of positive-width integer rectangles covering $\mathbb R^d$, with distinct tile interiors disjoint and each side length at most $K_i$. Only finitely many tiles contain a given point $x$. Intersect their faces containing $x$ to obtain its point-cell $C_T(x)$:
--   $$C_T(x)=\bigcap_{\substack{R\in T\\x\in R}} \operatorname{face}_R(x).$$
--   The point $x$ lies in the relative interior of $C_T(x)$, and $C_T(y)=C_T(x)$ throughout that relative interior. If $y\in C_T(x)$, then $C_T(y)\subseteq C_T(x)$. The resulting cells have disjoint relative interiors, inherit the side bounds, and only finitely many are contained in any fixed integer rectangle.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RectangularBoundaryStrata.lean, selected declaration lines 15-21, 26-30, 32-33, 35-36, 38-40, 42-44, 46-55, 57-59, 61-65, 67-71, 73-79, 81-85, 87-100, 102-110, 112, 118-124, 126-133, 140-145; SHA-256 1adbeb09ba61646fe8f126c03dba81801db0e75e1c8c2bc2ea989660bb309ae6. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_IntegerRectangleProbes
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularFaceRefinement
import Definitions.Def_AT260939824_RectangularLocalFiniteness
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Actual boundary strata of a bounded integer rectangular tiling

The cell at a point is the finite intersection of the minimal faces of
all incident full tiles. Integer probes prove that its relative interior
has exactly the same tile incidences. Thus the distinct point cells give
a relative-interior partition, with only tile boundaries refined.
-/

namespace AbelianTargets
noncomputable section

structure IntegerRectangularTiling (d : ℕ) (K : Fin d → ℕ) where
  tiles : Set (RectangularCell d)
  positive : ∀ R ∈ tiles,∀ i,R.lower i < R.upper i
  cover : ∀ z : RealCoordinates d,∃ R ∈ tiles,z ∈ R.closedBox
  interior_unique : ∀ R ∈ tiles,∀ Q ∈ tiles,
    (R.relativeInterior ∩ Q.relativeInterior).Nonempty → R = Q
  bounded : ∀ R ∈ tiles,R.HasBoundedSides K

namespace IntegerRectangularTiling
variable {d : ℕ} {K : Fin d → ℕ} (T : IntegerRectangularTiling d K)

theorem finite_incident (x : RealCoordinates d) :
    {R : RectangularCell d | R ∈ T.tiles ∧ x ∈ R.closedBox}.Finite := by
  apply (RectangularCell.finite_meeting_ball K x).subset
  intro R hR
  exact ⟨T.bounded R hR.1,x,hR.2,Metric.mem_ball_self (by norm_num)⟩

def incidentFinset (x : RealCoordinates d) : Finset (RectangularCell d) :=
  (T.finite_incident x).toFinset

@[simp] theorem mem_incidentFinset (x : RealCoordinates d) (R : RectangularCell d) :
    R ∈ T.incidentFinset x ↔ R ∈ T.tiles ∧ x ∈ R.closedBox := Set.Finite.mem_toFinset _

theorem incidentFinset_nonempty (x : RealCoordinates d) : (T.incidentFinset x).Nonempty := by
  obtain ⟨R,hR,hx⟩ := T.cover x
  exact ⟨R,(T.mem_incidentFinset x R).mpr ⟨hR,hx⟩⟩

def pointCell (x : RealCoordinates d) : RectangularCell d :=
  RectangularCell.faceIntersection (T.incidentFinset x) (T.incidentFinset_nonempty x) x
    (fun R hR => ((T.mem_incidentFinset x R).mp hR).2)

theorem mem_pointCell (x z : RealCoordinates d) :
    z ∈ (T.pointCell x).closedBox ↔
      ∀ R ∈ T.tiles,x ∈ R.closedBox → z ∈ (R.faceAt x).closedBox := by
  rw [pointCell,RectangularCell.mem_faceIntersection]
  constructor
  · intro h R hR hx
    exact h R ((T.mem_incidentFinset x R).mpr ⟨hR,hx⟩)
  · intro h R hR
    obtain ⟨hR,hx⟩ := (T.mem_incidentFinset x R).mp hR
    exact h R hR hx

theorem mem_relativeInterior_pointCell (x : RealCoordinates d) :
    x ∈ (T.pointCell x).relativeInterior :=
  RectangularCell.mem_relativeInterior_faceIntersection _ _ _ _

theorem pointCell_relativeInterior_subset_face (x : RealCoordinates d)
    {R : RectangularCell d} (hR : R ∈ T.tiles) (hx : x ∈ R.closedBox) :
    (T.pointCell x).relativeInterior ⊆ (R.faceAt x).relativeInterior :=
  RectangularCell.faceIntersection_relativeInterior_subset _ _ _ _
    ((T.mem_incidentFinset x R).mpr ⟨hR,hx⟩)

theorem pointCell_subset_tile (x : RealCoordinates d)
    {R : RectangularCell d} (hR : R ∈ T.tiles) (hx : x ∈ R.closedBox) :
    (T.pointCell x).closedBox ⊆ R.closedBox := by
  intro z hz
  exact R.faceAt_subset x ((T.mem_pointCell x z).mp hz R hR hx)

theorem pointCell_incident_faces (x y : RealCoordinates d)
    (hy : y ∈ (T.pointCell x).relativeInterior) :
    ∀ R ∈ T.tiles,x ∈ R.closedBox → y ∈ R.closedBox ∧ R.faceAt x = R.faceAt y := by
  intro R hR hx
  have hyface := T.pointCell_relativeInterior_subset_face x hR hx hy
  exact ⟨R.faceAt_subset x ((R.faceAt x).relativeInterior_subset hyface),
    (R.faceAt_eq_of_relativeInterior (T.positive R hR) x y hyface).symm⟩

theorem pointCell_incident_constant (x y : RealCoordinates d)
    (hy : y ∈ (T.pointCell x).relativeInterior) :
    ∀ R ∈ T.tiles,y ∈ R.closedBox ↔ x ∈ R.closedBox :=
  incident_tiles_constant_of_faces T.tiles T.positive T.cover T.interior_unique x y
    (T.pointCell_incident_faces x y hy)

theorem pointCell_constant (x y : RealCoordinates d)
    (hy : y ∈ (T.pointCell x).relativeInterior) : T.pointCell y = T.pointCell x := by
  apply RectangularCell.closedBox_injective
  ext z
  rw [T.mem_pointCell y z,T.mem_pointCell x z]
  constructor
  · intro h R hR hx
    have hyR := (T.pointCell_incident_constant x y hy R hR).mpr hx
    have he := (T.pointCell_incident_faces x y hy R hR hx).2
    simpa only [he] using h R hR hyR
  · intro h R hR hyR
    have hx := (T.pointCell_incident_constant x y hy R hR).mp hyR
    have he := (T.pointCell_incident_faces x y hy R hR hx).2
    simpa only [he] using h R hR hx

theorem pointCell_closed_mono (x z : RealCoordinates d)
    (hz : z ∈ (T.pointCell x).closedBox) :
    (T.pointCell z).closedBox ⊆ (T.pointCell x).closedBox := by
  intro w hw
  apply (T.mem_pointCell x w).mpr
  intro R hR hx
  have hzface := (T.mem_pointCell x z).mp hz R hR hx
  have hzR := R.faceAt_subset x hzface
  exact R.faceAt_mono (T.positive R hR) x z hzface ((T.mem_pointCell z w).mp hw R hR hzR)

def cells : Set (RectangularCell d) := Set.range T.pointCell



theorem relativeInterior_unique {R Q : RectangularCell d}
    (hR : R ∈ T.cells) (hQ : Q ∈ T.cells)
    (hz : (R.relativeInterior ∩ Q.relativeInterior).Nonempty) : R = Q := by
  obtain ⟨x,rfl⟩ := hR
  obtain ⟨y,rfl⟩ := hQ
  obtain ⟨z,hzx,hzy⟩ := hz
  exact (T.pointCell_constant x z hzx).symm.trans (T.pointCell_constant y z hzy)

theorem cells_bounded {R : RectangularCell d} (hR : R ∈ T.cells) : R.HasBoundedSides K := by
  obtain ⟨x,rfl⟩ := hR
  obtain ⟨Q,hQ,hxQ⟩ := T.cover x
  have hsub := (RectangularCell.closedBox_subset_iff _ _).mp (T.pointCell_subset_tile x hQ hxQ)
  intro i
  have hQbound := T.bounded Q hQ i
  have hi := hsub i
  omega



theorem finite_cells_contained (R : RectangularCell d) :
    {Q : RectangularCell d | Q ∈ T.cells ∧ Q.closedBox ⊆ R.closedBox}.Finite := by
  apply (RectangularCell.finite_bounded_endpoints R.lower R.upper).subset
  intro Q hQ i
  have hi := (RectangularCell.closedBox_subset_iff Q R).mp hQ.2 i
  exact ⟨hi.1,(Q.ordered i).trans hi.2,hi.1.trans (Q.ordered i),hi.2⟩

end IntegerRectangularTiling
end
end AbelianTargets


