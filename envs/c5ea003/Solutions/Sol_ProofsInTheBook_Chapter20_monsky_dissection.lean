-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.monsky_dissection
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T18:30:42.556426+00:00
-- url     : https://prove2.me/submissions/87401a7a-5d4b-4796-ba7b-e0c9cd1df717

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
import Theorems.Thm_ProofsInTheBook_Chapter20_Chapter20E2Frontier_frontier_unitSquare
import Theorems.Thm_ProofsInTheBook_Chapter20_atomicBoundary_mem_squareBoundaryEdgeList_of_square_corners
import Theorems.Thm_ProofsInTheBook_Chapter20_atomicMult_eq_one_of_boundary
import Theorems.Thm_ProofsInTheBook_Chapter20_atomicMult_even_of_interior
import Theorems.Thm_ProofsInTheBook_Chapter20_endpoints_mem_of_mem_consecutiveEdges_local
import Theorems.Thm_ProofsInTheBook_Chapter20_isAtomic_of_mem_squareSideAtomicEdges
import Theorems.Thm_ProofsInTheBook_Chapter20_mem_segment_unit_left
import Theorems.Thm_ProofsInTheBook_Chapter20_mem_segment_unit_top
import Theorems.Thm_ProofsInTheBook_Chapter20_monsky_false_of_odd_corner_parity
import Theorems.Thm_ProofsInTheBook_Chapter20_squareBoundaryEdgeList_nodup_of_square_corners
import Theorems.Thm_ProofsInTheBook_Chapter20_squareBoundaryVertexChainRGCount_odd_of_side_colors
import Theorems.Thm_ProofsInTheBook_Chapter20_sum_triangleLocalRGCount_mod_two_eq_oddAtomic


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter20 -/
section
set_option autoImplicit true


/-!
# Chapter 20: One square and an odd number of triangles

From "Proofs from THE BOOK":

**Monsky's theorem**: A square cannot be divided into an odd number
of triangles of equal area.

The book's proof uses a 2-adic valuation argument: define a coloring
of the plane using the 2-adic valuation of coordinates, then apply
Sperner's lemma to show the triangulation must have an even count.

Formalization status: this file closes the finite coloring and parity layer.
It defines Monsky's three colors, red-green boundary edges, trichromatic
triangles, proves the local parity identity, proves an abstract Sperner
parity theorem, and derives `chapter20`: a `MonskyCertificate n` yields a
trichromatic triangle.  It also packages Mathlib's local-subring/Zorn
infrastructure into `exists_valuation_extension`, which gives an extension of
any valuation on a field to any field extension; in particular
`exists_real_twoAdic_extension` extends `Rat.padicValuation 2` from `ℚ` to `ℝ`.
Using one chosen extension, the file defines Monsky's coloring on `ℝ²`, proves
the unit-square side color constraints, proves the odd red-green boundary
count for any finite subdivision of the square boundary, identifies that count
with an explicit finite list of unit-square boundary point-edges, constructs
`MonskyCertificate` from finite unordered-edge parity, and proves the valuation
contradiction for a trichromatic triangle of ordinary real area `1 / n` with
`n` odd.

Gap to the full book theorem: the remaining work is geometric triangulation
infrastructure.  One needs a finite real triangulation model for the unit
square and an extraction theorem producing:
1. a finite vertex type `α`, a point map `vertices : α → ℝ × ℝ`, and triangles
   `triangles : Fin n → α × α × α`;
2. four side subdivision lists `bottom right top left : List ℝ`, or equivalently
   the explicit point-edge chain `realTwoAdicSquareBoundaryPointEdgeList`;
3. the boundary-incidence theorem that the odd-multiplicity triangle edges are
   exactly that square boundary chain after mapping boundary points to the
   finite vertex type;
4. the ordinary equal-area fact
   `∀ i, realTriangleArea ... = (1 / n : ℚ)`.
Mathlib has `Analysis.Convex.SimplicialComplex` and `Geometry.Polygon.Basic`,
but not this assembled theorem extracting boundary chains and equal-area facts
from a triangulation of the unit square.
-/

namespace ProofsInTheBook.Chapter20

open IsLocalRing









open MonskyColor













theorem colorOfValues_zero_right_red_or_green {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vx : Γ) : colorOfValues vx 0 = red ∨ colorOfValues vx 0 = green := by
  unfold colorOfValues
  by_cases hx : vx < 1
  · simp [hx]
  · have hxge : 1 ≤ vx := le_of_not_gt hx
    right
    simp [hx, hxge]

theorem colorOfValues_one_left_green_or_blue {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vy : Γ) : colorOfValues 1 vy = green ∨ colorOfValues 1 vy = blue := by
  unfold colorOfValues
  by_cases hy : vy ≤ 1
  · left
    simp [hy]
  · right
    simp [hy]

theorem colorOfValues_one_right_green_or_blue {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vx : Γ) : colorOfValues vx 1 = green ∨ colorOfValues vx 1 = blue := by
  unfold colorOfValues
  by_cases hx : 1 ≤ vx
  · left
    simp [hx]
  · right
    have hxlt : vx < 1 := lt_of_not_ge hx
    simp [hx, hxlt]

theorem colorOfValues_zero_left_red_or_blue {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vy : Γ) : colorOfValues 0 vy = red ∨ colorOfValues 0 vy = blue := by
  unfold colorOfValues
  by_cases hy : vy < 1
  · left
    simp [hy]
  · right
    simp [hy]















































@[simp]
theorem realTwoAdicColor_origin : realTwoAdicColor (0, 0) = red := by
  simp [realTwoAdicColor, valuationColor, colorOfValues, realTwoAdicValuation]

@[simp]
theorem realTwoAdicColor_one_zero : realTwoAdicColor (1, 0) = green := by
  simp [realTwoAdicColor, valuationColor, colorOfValues, realTwoAdicValuation]

@[simp]
theorem realTwoAdicColor_zero_one : realTwoAdicColor (0, 1) = blue := by
  simp [realTwoAdicColor, valuationColor, colorOfValues, realTwoAdicValuation]

@[simp]
theorem realTwoAdicColor_one_one : realTwoAdicColor (1, 1) = green := by
  simp [realTwoAdicColor, valuationColor, colorOfValues, realTwoAdicValuation]

theorem realTwoAdicColor_bottom_red_or_green (x : ℝ) :
    realTwoAdicColor (x, 0) = red ∨ realTwoAdicColor (x, 0) = green := by
  simpa [realTwoAdicColor, valuationColor] using
    colorOfValues_zero_right_red_or_green (realTwoAdicValuation x)

theorem realTwoAdicColor_right_green_or_blue (y : ℝ) :
    realTwoAdicColor (1, y) = green ∨ realTwoAdicColor (1, y) = blue := by
  simpa [realTwoAdicColor, valuationColor] using
    colorOfValues_one_left_green_or_blue (realTwoAdicValuation y)

theorem realTwoAdicColor_top_green_or_blue (x : ℝ) :
    realTwoAdicColor (x, 1) = green ∨ realTwoAdicColor (x, 1) = blue := by
  simpa [realTwoAdicColor, valuationColor] using
    colorOfValues_one_right_green_or_blue (realTwoAdicValuation x)

theorem realTwoAdicColor_left_red_or_blue (y : ℝ) :
    realTwoAdicColor (0, y) = red ∨ realTwoAdicColor (0, y) = blue := by
  simpa [realTwoAdicColor, valuationColor] using
    colorOfValues_zero_left_red_or_blue (realTwoAdicValuation y)



































































































































theorem boundaryEdgeRedGreenCount_toFinset {α : Type*} [DecidableEq α]
    (edges : List (Sym2 α)) (color : α → MonskyColor) (hnodup : edges.Nodup) :
    boundaryEdgeRedGreenCount edges.toFinset color = listEdgeRGCount edges color := by
  classical
  unfold boundaryEdgeRedGreenCount listEdgeRGCount
  have htf : (edges.filter fun e => edgeRGIndicator color e = 1).toFinset =
      edges.toFinset.filter fun e => edgeRGIndicator color e = 1 := by
    ext e
    simp
  rw [← htf]
  exact List.toFinset_card_of_nodup (hnodup.filter _)



































/-
Remaining geometric interface: given a hypothetical equal-area triangulation
of the unit square into an odd number of real triangles, one still needs to
extract the finite list of triangle vertices, identify the odd-multiplicity
triangle edges with the explicit square boundary point-edge chain, and express
the equal-area hypothesis as oriented double area `± 2 / n` for each listed
triangle.
-/



















































/-! ### Linear-algebra bridge for `doubleArea`

The signed double-area `doubleArea a b c` is the determinant of the linear map
on `ℝ²` whose standard-basis images are the edge vectors `b - a` and `c - a`.
This rephrasing is the foundation for connecting the chapter's combinatorial
oriented area to Mathlib's `addHaar_image_linearMap` change-of-variables
formula — the route by which a future geometric dissection of the unit square
will deliver the boundary edge-parity (`hboundary`) needed to remove the
remaining `MonskyCertificate` escape.
-/





/-! ### Structural properties of `doubleArea`

Translation invariance, vertex-permutation symmetries, and the collinearity
equivalence — small structural lemmas needed for any future geometric work
on triangle dissections of the unit square (Monsky's remaining frontier).
-/



















/-! ### Affine parametrization of the triangle by the filled 2-simplex

The triangle with vertices `a, b, c` is the image, under the affine map
`(s, t) ↦ a + s • (b - a) + t • (c - a)`, of the filled standard 2-simplex
`{(s, t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}`.  We define the parametrization and
prove the forward containment (image ⊆ convex hull).  Pairing this with the
2-dimensional Lebesgue volume formula for linear-map images is the route to
`volume (convexHull ℝ {a, b, c}) = realTriangleArea a b c`.
-/



















/-! ### Brick 1: volume of the filled 2-simplex

The 2-dimensional Lebesgue measure of `filled2Simplex` equals `1/2`.
Direct Fubini route: slice the simplex at fixed `x`, identify the slice
with `Icc 0 (1-x)`, and integrate the linear height. -/









/-! ### Brick 2: convex hull ⊆ triangleAffine image

The reverse inclusion `convexHull ℝ {a, b, c} ⊆ triangleAffine '' filled2Simplex`
combined with `triangleAffine_image_subset_convexHull` gives set equality. -/











/-! ### Brick 3: glue to `volume_convexHull_triangle`

The measure-theoretic bridge for Monsky's chapter 20:
`volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (realTriangleArea a b c)`. -/















/-! ### Packaged triangulation API

A `RealEqualAreaUnitSquareTriangulation α n` bundles the finite-vertex data
the Monsky frontier theorem
`no_odd_equalArea_realization_of_realSquareBoundaryVertexChain_area` consumes.
This is a refactoring layer: every hypothesis the existing theorem takes is
folded into a single named field, so downstream callers only need to construct
one structure instead of supplying twenty-plus arguments. -/





/-! ### Concrete witness: the diagonal split

The unit square can be split into two triangles of area 1/2 each by the main
diagonal — a constructive `RealEqualAreaUnitSquareTriangulation (Fin 4) 2`.
This is also a non-vacuity check on the packaged API: the structure can be
inhabited, just not for odd `n`. -/

namespace RealEqualAreaUnitSquareTriangulation





end RealEqualAreaUnitSquareTriangulation

end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20E2Frontier -/
section
set_option autoImplicit true


/-!
# Chapter 20 E2 frontier geometry

Auxiliary planar convex-geometry lemmas for the E2 incidence proof.
-/

namespace ProofsInTheBook.Chapter20

open scoped Topology

namespace Chapter20E2Frontier



























































end Chapter20E2Frontier

export Chapter20E2Frontier
  (
   
   
   
   
   
   
   
   
   
   
   
   frontier_unitSquare)

end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20E2Frontier
-/
/- Source module: ProofsInTheBook.Chapter20E2Cover -/
section
set_option autoImplicit true


/-!
# Chapter 20 E2 cover lemmas

General connected-cover packaging for the local E2 incidence argument.
-/

namespace ProofsInTheBook.Chapter20

open scoped Topology
open Set

namespace Chapter20E2Cover













end Chapter20E2Cover



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20E2Cover
-/
/- Source module: ProofsInTheBook.Chapter20DissectionEngine -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — dissection engine (atomic incidence + reduction to E2)

This file defines a genuine `SquareDissection` (finite triangles, pairwise
disjoint interiors, union the unit square, equal area `1/n`), the atomic-segment
incidence built from it, and reduces Monsky's theorem to the single geometric
incidence fact **E2** (`atomicMult_even_of_interior` / `atomicMult_eq_one_of_boundary`).

The E2 statements are proved here as the main convex-geometry brick
(see `HANDOFF/CH20_E2_SPEC.md`).
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor
open scoped Topology





variable (D : SquareDissection)







































































































































































































































































/-! ### E2 — the geometric incidence core (the single heavy brick) -/





end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20Dissection -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — faithful dissection front end

`Chapter20.lean` proves Monsky's theorem **conditional on** the structure field
`RealEqualAreaUnitSquareTriangulation.hboundary`, which states that an unordered
*full* triangle edge `s(p, r) : Sym2 α` has odd triangle-multiplicity iff it lies
on the square boundary.  That is the *edge-to-edge* (simplicial) special case:
it fails for a genuine dissection in which a triangle side `p–r` is subdivided by
a "T-vertex" `m` belonging to neighbouring triangles, because then `s(p, r)` has
multiplicity `1` (odd) yet is interior.

Monsky's theorem is about **arbitrary** dissections.  The book (Aigner–Ziegler,
Ch. 20, Lemma 2) counts *atomic segments between consecutive vertices* and uses
"every red–green segment in the interior is counted twice".  This file builds
that faithful atomic-segment front end on top of the proved valuation / Sperner
engine in `Chapter20.lean`.

Sub-facts (book Lemma 2):
* **E2** each interior atomic segment lies on exactly two triangle boundaries,
  each boundary atomic segment on exactly one  *(the geometric core)*;
* **E3** on any straight side, the number of red–green atomic segments has the
  parity of `[endpoints are red&green]`, from the ≤2-colors-per-line corollary;
* **E5** the bottom side carries an odd number of red–green atomic segments and
  the other three sides carry none.

This file currently establishes the **≤2-colors-per-line corollary** to Lemma 1,
the foundation E3 rests on.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor





/-! ### E3 — per-side red–green parity (general, from ≤2 colors per line)

Along one straight side of a triangle the dissection vertices form a chain
`a :: middle ++ [b]` lying on a single line, so by the ≤2-colors corollary the
chain uses at most two of the three colors.  In that situation the number of
red–green atomic segments along the chain has exactly the parity of "the two
endpoints `a, b` form a red–green pair".  This upgrades the proved
`listRGTransitionCount_*` side lemmas (which fix the colors per side) to an
arbitrary side of an arbitrary triangle. -/



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20Dissection
-/
/- Source module: ProofsInTheBook.Chapter20Colors -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — collinear-list colour lemmas (E3 plumbing)

The ≤2-colours-per-line corollary (`not_trichromatic_of_collinear`) upgraded
from a single triple to a whole collinear list of points: a list in which every
triple is collinear omits at least one of the three Monsky colours, hence uses at
most two.  Combined with E3 (`odd_listRGTransitionCount_iff_endpoints`) this gives
the per-side red–green parity for an arbitrary subdivided triangle side.

Depends only on `Chapter20Dissection` (brick-1 + E3); independent of the geometric
`SquareDissection` definition, so it is stable while that is under construction.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor







end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20AtomicCount -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — abstract atomic double-count

The list-multiplicity analogue of the full-edge double-count
`sum_triangleLocalRGCount_mod_two_eq_oddEdgeRedGreenCount`.  Stated abstractly
for a finite family of edge-lists `f : Fin n → List (Sym2 V)`, so the dissection
engine instantiates it with `f := triAtomicEdges D`.  Engine-independent: depends
only on `Chapter20`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable {V : Type*} [Fintype V] [DecidableEq V]













end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20SideGeom -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — side collinearity

The geometric fact behind the per-side E3 bridge: any three points lying on a
common segment `[P, Q]` are collinear, i.e. their signed double area vanishes.
Used to feed `exists_two_colors_of_collinear_list` for each subdivided triangle
side.  Engine-independent (raw points), instantiated later with vertex coords.
-/

namespace ProofsInTheBook.Chapter20



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20DissectionSperner -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — Sperner→contradiction spine

The engine-independent capstone spine: given a finite family of real triangles
each of area `1/n` (`n` odd) and the parity fact that the summed corner
red–green count is odd, Monsky's coloring forces a rainbow triangle whose area
cannot be `1/n` — contradiction.  This packages
`exists_trichromatic_of_odd_boundary` with
`not_real_triangleArea_eq_one_div_odd_of_trichromatic`, leaving the dissection
engine only to supply the parity hypothesis (`hparity`).

Depends only on `Chapter20`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20DissectionEngine
import ProofsInTheBook.Chapter20E2Frontier
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20E2Boundary -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — boundary atomic red-green parity

This file contains the boundary half of the atomic E2 bookkeeping: the
red-green atomic edges with odd atomic multiplicity are odd in number.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable (D : SquareDissection)

open scoped Classical in
lemma atomicMult_eq_zero_of_not_isAtomic {e : Sym2 D.vtx}
    (he : ¬ IsAtomicEdge D e) :
    atomicMult D e = 0 := by
  classical
  unfold atomicMult
  refine Finset.sum_eq_zero fun i _ => ?_
  have hnot : e ∉ triAtomicEdges D i := by
    intro hi
    exact he ⟨i, hi⟩
  exact List.count_eq_zero_of_not_mem hnot

open scoped Classical in
lemma isAtomic_of_odd_atomicMult {e : Sym2 D.vtx}
    (hodd : Odd (atomicMult D e)) :
    IsAtomicEdge D e := by
  classical
  by_contra he
  have hzero := atomicMult_eq_zero_of_not_isAtomic (D := D) (e := e) he
  simp [hzero] at hodd

open scoped Classical in
lemma odd_atomicMult_iff_isAtomic_boundary (e : Sym2 D.vtx) :
    Odd (atomicMult D e) ↔ IsAtomicEdge D e ∧ OnSquareBoundary D e := by
  classical
  constructor
  · intro hodd
    have he : IsAtomicEdge D e := isAtomic_of_odd_atomicMult (D := D) hodd
    refine ⟨he, ?_⟩
    by_contra hbd
    have hev := atomicMult_even_of_interior D e he hbd
    exact Nat.not_even_iff_odd.mpr hodd hev
  · rintro ⟨he, hbd⟩
    have hone := atomicMult_eq_one_of_boundary D e he hbd
    rw [hone]
    exact odd_one

open scoped Classical in
lemma oddAtomicRG_filter_eq_atomicBoundaryRG :
    (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧ Odd (atomicMult D e)) =
    (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
        IsAtomicEdge D e ∧ OnSquareBoundary D e) := by
  classical
  ext e
  simp [odd_atomicMult_iff_isAtomic_boundary (D := D) e]

lemma unitSquare_corner00_extreme :
    ((0, 0) : ℝ × ℝ) ∈
      (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ := by
  have hsquare :
      Set.Icc ((0, 0) : ℝ × ℝ) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, extremePoints_prod]
  simp [Set.extremePoints_Icc]

lemma unitSquare_corner10_extreme :
    ((1, 0) : ℝ × ℝ) ∈
      (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ := by
  have hsquare :
      Set.Icc ((0, 0) : ℝ × ℝ) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, extremePoints_prod]
  simp [Set.extremePoints_Icc]

lemma unitSquare_corner11_extreme :
    ((1, 1) : ℝ × ℝ) ∈
      (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ := by
  have hsquare :
      Set.Icc ((0, 0) : ℝ × ℝ) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, extremePoints_prod]
  simp [Set.extremePoints_Icc]

lemma unitSquare_corner01_extreme :
    ((0, 1) : ℝ × ℝ) ∈
      (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ := by
  have hsquare :
      Set.Icc ((0, 0) : ℝ × ℝ) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, extremePoints_prod]
  simp [Set.extremePoints_Icc]

lemma exists_vertex_coord_of_extreme_unitSquare {c : ℝ × ℝ}
    (hc : c ∈ (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)).extremePoints ℝ) :
    ∃ v : D.vtx, D.coord v = c := by
  let square : Set (ℝ × ℝ) := Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)
  have hc_mem : c ∈ square := by
    simpa [square] using extremePoints_subset hc
  have hcover_mem : c ∈ ⋃ i : Fin D.n, convexHull ℝ
      {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2} := by
    simpa [square, D.cover] using hc_mem
  rcases Set.mem_iUnion.mp hcover_mem with ⟨i, hi⟩
  let T : Set (ℝ × ℝ) := convexHull ℝ
      {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2}
  have hTsubset : T ⊆ square := by
    intro x hx
    have hxUnion : x ∈ ⋃ j : Fin D.n, convexHull ℝ
        {D.coord (D.tri j).1, D.coord (D.tri j).2.1, D.coord (D.tri j).2.2} := by
      exact Set.mem_iUnion.mpr ⟨i, by simpa [T] using hx⟩
    simpa [square, D.cover] using hxUnion
  have hcT : c ∈ T := by
    simpa [T] using hi
  have hsqExtreme : IsExtreme ℝ square {c} := by
    rw [isExtreme_singleton]
    simpa [square] using hc
  have hTExtremeSet : IsExtreme ℝ T {c} := by
    exact hsqExtreme.mono hTsubset (by simpa using hcT)
  have hcTExtreme : c ∈ T.extremePoints ℝ := by
    rw [← isExtreme_singleton]
    exact hTExtremeSet
  have hmemVerts : c ∈ ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
      D.coord (D.tri i).2.2} : Set (ℝ × ℝ)) := by
    have h := extremePoints_convexHull_subset (𝕜 := ℝ)
      (A := ({D.coord (D.tri i).1, D.coord (D.tri i).2.1,
        D.coord (D.tri i).2.2} : Set (ℝ × ℝ))) hcTExtreme
    simpa [T] using h
  rcases hmemVerts with h | h | h
  · exact ⟨(D.tri i).1, h.symm⟩
  · exact ⟨(D.tri i).2.1, h.symm⟩
  · exact ⟨(D.tri i).2.2, h.symm⟩

lemma exists_square_corners :
    ∃ c00 c10 c11 c01 : D.vtx,
      D.coord c00 = (0, 0) ∧ D.coord c10 = (1, 0) ∧
      D.coord c11 = (1, 1) ∧ D.coord c01 = (0, 1) := by
  obtain ⟨c00, h00⟩ :=
    exists_vertex_coord_of_extreme_unitSquare (D := D) unitSquare_corner00_extreme
  obtain ⟨c10, h10⟩ :=
    exists_vertex_coord_of_extreme_unitSquare (D := D) unitSquare_corner10_extreme
  obtain ⟨c11, h11⟩ :=
    exists_vertex_coord_of_extreme_unitSquare (D := D) unitSquare_corner11_extreme
  obtain ⟨c01, h01⟩ :=
    exists_vertex_coord_of_extreme_unitSquare (D := D) unitSquare_corner01_extreme
  exact ⟨c00, c10, c11, c01, h00, h10, h11, h01⟩









open scoped Classical in
lemma mem_sideInteriorChain_iff_local {p q w : D.vtx} :
    w ∈ sideInteriorChain D p q ↔ OnSide D p q w ∧ w ≠ p ∧ w ≠ q := by
  classical
  unfold sideInteriorChain
  rw [List.mem_insertionSort, Finset.mem_toList]
  simp [OnSide]

















lemma onSide_left_local (p q : D.vtx) : OnSide D p q p := by
  exact wbtw_self_left (R := ℝ) (D.coord p) (D.coord q)

lemma onSide_right_local (p q : D.vtx) : OnSide D p q q := by
  exact wbtw_self_right (R := ℝ) (D.coord p) (D.coord q)

lemma sideInteriorChain_onSide_local {p q w : D.vtx}
    (hw : w ∈ sideInteriorChain D p q) : OnSide D p q w :=
  (mem_sideInteriorChain_iff_local (D := D)).mp hw |>.1

lemma onSide_of_mem_sideChain_local {p q w : D.vtx}
    (hw : w ∈ p :: sideInteriorChain D p q ++ [q]) : OnSide D p q w := by
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · rw [List.mem_cons] at hw
    rcases hw with hwp | hw
    · rw [hwp]
      exact onSide_left_local D p q
    · exact sideInteriorChain_onSide_local D hw
  · rw [List.mem_singleton] at hw
    rw [hw]
    exact onSide_right_local D p q

lemma endpoints_onSide_of_mem_sideAtomicEdges_local {p q a b : D.vtx}
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    OnSide D p q a ∧ OnSide D p q b := by
  unfold sideAtomicEdges at h
  have hend := endpoints_mem_of_mem_consecutiveEdges_local h
  exact ⟨onSide_of_mem_sideChain_local D hend.1,
    onSide_of_mem_sideChain_local D hend.2⟩









































lemma segment_subset_of_onSide_local {p q a b : D.vtx}
    (ha : OnSide D p q a) (hb : OnSide D p q b) :
    segment ℝ (D.coord a) (D.coord b) ⊆ segment ℝ (D.coord p) (D.coord q) := by
  exact (convex_segment (D.coord p) (D.coord q)).segment_subset
    (Wbtw.mem_segment ha) (Wbtw.mem_segment hb)

















lemma coord_bottom_of_onSide {p q v : D.vtx}
    (hp : D.coord p = (0, 0)) (hq : D.coord q = (1, 0))
    (h : OnSide D p q v) :
    ∃ x : ℝ, D.coord v = (x, 0) := by
  unfold OnSide at h
  obtain ⟨t, _ht, hv⟩ := h
  refine ⟨(D.coord v).1, ?_⟩
  ext
  · rfl
  · have hy := congrArg Prod.snd hv
    simpa [hp, hq, AffineMap.lineMap_apply] using hy.symm

lemma coord_right_of_onSide {p q v : D.vtx}
    (hp : D.coord p = (1, 0)) (hq : D.coord q = (1, 1))
    (h : OnSide D p q v) :
    ∃ y : ℝ, D.coord v = (1, y) := by
  unfold OnSide at h
  obtain ⟨t, _ht, hv⟩ := h
  refine ⟨(D.coord v).2, ?_⟩
  ext
  · have hx := congrArg Prod.fst hv
    simpa [hp, hq, AffineMap.lineMap_apply] using hx.symm
  · rfl

lemma coord_top_of_onSide {p q v : D.vtx}
    (hp : D.coord p = (1, 1)) (hq : D.coord q = (0, 1))
    (h : OnSide D p q v) :
    ∃ x : ℝ, D.coord v = (x, 1) := by
  unfold OnSide at h
  obtain ⟨t, _ht, hv⟩ := h
  refine ⟨(D.coord v).1, ?_⟩
  ext
  · rfl
  · have hy := congrArg Prod.snd hv
    simpa [hp, hq, AffineMap.lineMap_apply] using hy.symm

lemma coord_left_of_onSide {p q v : D.vtx}
    (hp : D.coord p = (0, 1)) (hq : D.coord q = (0, 0))
    (h : OnSide D p q v) :
    ∃ y : ℝ, D.coord v = (0, y) := by
  unfold OnSide at h
  obtain ⟨t, _ht, hv⟩ := h
  refine ⟨(D.coord v).2, ?_⟩
  ext
  · have hx := congrArg Prod.fst hv
    simpa [hp, hq, AffineMap.lineMap_apply] using hx.symm
  · rfl

lemma mem_segment_unit_bottom (p : ℝ × ℝ) :
    p ∈ segment ℝ ((0, 0) : ℝ × ℝ) (1, 0) ↔
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 0 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [AffineMap.lineMap_apply] using ht
  · intro hp
    refine ⟨p.1, ⟨hp.1, hp.2.1⟩, ?_⟩
    ext <;> simp [AffineMap.lineMap_apply, hp.2.2]

lemma mem_segment_unit_right (p : ℝ × ℝ) :
    p ∈ segment ℝ ((1, 0) : ℝ × ℝ) (1, 1) ↔
      p.1 = 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [AffineMap.lineMap_apply] using ht
  · intro hp
    refine ⟨p.2, ⟨hp.2.1, hp.2.2⟩, ?_⟩
    ext <;> simp [AffineMap.lineMap_apply, hp.1]





lemma onSide_bottom_of_coord {c00 c10 v : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (hx0 : 0 ≤ (D.coord v).1) (hx1 : (D.coord v).1 ≤ 1)
    (hy : (D.coord v).2 = 0) :
    OnSide D c00 c10 v := by
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ)]
  rw [h00, h10, mem_segment_unit_bottom]
  exact ⟨hx0, hx1, hy⟩

lemma onSide_right_of_coord {c10 c11 v : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1))
    (hx : (D.coord v).1 = 1) (hy0 : 0 ≤ (D.coord v).2)
    (hy1 : (D.coord v).2 ≤ 1) :
    OnSide D c10 c11 v := by
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ)]
  rw [h10, h11, mem_segment_unit_right]
  exact ⟨hx, hy0, hy1⟩

lemma onSide_top_of_coord {c11 c01 v : D.vtx}
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (hx0 : 0 ≤ (D.coord v).1) (hx1 : (D.coord v).1 ≤ 1)
    (hy : (D.coord v).2 = 1) :
    OnSide D c11 c01 v := by
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ)]
  rw [h11, h01, mem_segment_unit_top]
  exact ⟨hx0, hx1, hy⟩

lemma onSide_left_of_coord {c01 c00 v : D.vtx}
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0))
    (hx : (D.coord v).1 = 0) (hy0 : 0 ≤ (D.coord v).2)
    (hy1 : (D.coord v).2 ≤ 1) :
    OnSide D c01 c00 v := by
  unfold OnSide
  rw [← mem_segment_iff_wbtw (R := ℝ)]
  rw [h01, h00, mem_segment_unit_left]
  exact ⟨hx, hy0, hy1⟩

lemma bottom_segment_subset_frontier
    {c00 c10 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0)) :
    segment ℝ (D.coord c00) (D.coord c10) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  intro x hx
  rw [h00, h10, mem_segment_unit_bottom] at hx
  rw [frontier_unitSquare]
  exact ⟨hx.1, hx.2.1, by linarith, by linarith, Or.inr <| Or.inr <| Or.inl hx.2.2⟩

lemma right_segment_subset_frontier
    {c10 c11 : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1)) :
    segment ℝ (D.coord c10) (D.coord c11) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  intro x hx
  rw [h10, h11, mem_segment_unit_right] at hx
  rw [frontier_unitSquare]
  exact ⟨by linarith, by linarith, hx.2.1, hx.2.2, Or.inr <| Or.inl hx.1⟩

lemma top_segment_subset_frontier
    {c11 c01 : D.vtx}
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    segment ℝ (D.coord c11) (D.coord c01) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  intro x hx
  rw [h11, h01, mem_segment_unit_top] at hx
  rw [frontier_unitSquare]
  exact ⟨hx.1, hx.2.1, by linarith, by linarith, Or.inr <| Or.inr <| Or.inr hx.2.2⟩

lemma left_segment_subset_frontier
    {c01 c00 : D.vtx}
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0)) :
    segment ℝ (D.coord c01) (D.coord c00) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  intro x hx
  rw [h01, h00, mem_segment_unit_left] at hx
  rw [frontier_unitSquare]
  exact ⟨by linarith, by linarith, hx.2.1, hx.2.2, Or.inl hx.1⟩

lemma onSquareBoundary_mk_iff {a b : D.vtx} :
    OnSquareBoundary D s(a, b) ↔
      segment ℝ (D.coord a) (D.coord b) ⊆
        frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  rfl







lemma openSegment_endpoints_on_bottom_of_mem_unitSquare
    {u v m : ℝ × ℝ} (hu : u ∈ unitSquareSetLocal) (hv : v ∈ unitSquareSetLocal)
    (hm : m ∈ openSegment ℝ u v) (hmy : m.2 = 0) :
    u.2 = 0 ∧ v.2 = 0 := by
  have hu' : 0 ≤ u.2 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.2
  have hv' : 0 ≤ v.2 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.2
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨t, ht, hm⟩
  have hsnd := congrArg Prod.snd hm
  simp [hmy, Prod.smul_mk, Prod.mk_add_mk] at hsnd
  constructor <;> nlinarith [ht.1, ht.2, hu', hv', hsnd]

lemma openSegment_endpoints_on_top_of_mem_unitSquare
    {u v m : ℝ × ℝ} (hu : u ∈ unitSquareSetLocal) (hv : v ∈ unitSquareSetLocal)
    (hm : m ∈ openSegment ℝ u v) (hmy : m.2 = 1) :
    u.2 = 1 ∧ v.2 = 1 := by
  have hu' : u.2 ≤ 1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.2
  have hv' : v.2 ≤ 1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.2
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨t, ht, hm⟩
  have hsnd := congrArg Prod.snd hm
  simp [hmy, Prod.smul_mk, Prod.mk_add_mk] at hsnd
  constructor <;> nlinarith [ht.1, ht.2, hu', hv', hsnd]

lemma openSegment_endpoints_on_left_of_mem_unitSquare
    {u v m : ℝ × ℝ} (hu : u ∈ unitSquareSetLocal) (hv : v ∈ unitSquareSetLocal)
    (hm : m ∈ openSegment ℝ u v) (hmx : m.1 = 0) :
    u.1 = 0 ∧ v.1 = 0 := by
  have hu' : 0 ≤ u.1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.1
  have hv' : 0 ≤ v.1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.1
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨t, ht, hm⟩
  have hfst := congrArg Prod.fst hm
  simp [hmx, Prod.smul_mk, Prod.mk_add_mk] at hfst
  constructor <;> nlinarith [ht.1, ht.2, hu', hv', hfst]

lemma openSegment_endpoints_on_right_of_mem_unitSquare
    {u v m : ℝ × ℝ} (hu : u ∈ unitSquareSetLocal) (hv : v ∈ unitSquareSetLocal)
    (hm : m ∈ openSegment ℝ u v) (hmx : m.1 = 1) :
    u.1 = 1 ∧ v.1 = 1 := by
  have hu' : u.1 ≤ 1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.1
  have hv' : v.1 ≤ 1 := by
    simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.1
  rw [openSegment_eq_image] at hm
  rcases hm with ⟨t, ht, hm⟩
  have hfst := congrArg Prod.fst hm
  simp [hmx, Prod.smul_mk, Prod.mk_add_mk] at hfst
  constructor <;> nlinarith [ht.1, ht.2, hu', hv', hfst]



lemma bottom_squareSideAtomic_atomicBoundary
    {c00 c10 a b : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (hside : s(a, b) ∈ sideAtomicEdges D c00 c10) :
    IsAtomicEdge D s(a, b) ∧ OnSquareBoundary D s(a, b) := by
  have h0010 : c00 ≠ c10 := by
    intro h
    have : ((0, 0) : ℝ × ℝ) = (1, 0) := by
      rw [← h00, h, h10]
    norm_num at this
  have hfront := bottom_segment_subset_frontier (D := D) h00 h10
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hbd : OnSquareBoundary D s(a, b) := by
    rw [onSquareBoundary_mk_iff]
    exact (segment_subset_of_onSide_local D hon.1 hon.2).trans hfront
  have hatom : IsAtomicEdge D s(a, b) :=
    isAtomic_of_mem_squareSideAtomicEdges (D := D) h0010 hside hfront
      (fun u v hu hv hmopen => by
        have hmSide :
            midpoint ℝ (D.coord a) (D.coord b) ∈
              segment ℝ (D.coord c00) (D.coord c10) :=
          segment_subset_of_onSide_local D hon.1 hon.2
            (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
        have hmb := hmSide
        rw [h00, h10, mem_segment_unit_bottom] at hmb
        have huv_y := openSegment_endpoints_on_bottom_of_mem_unitSquare hu hv hmopen hmb.2.2
        have hux0 : 0 ≤ (D.coord u).1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.1
        have hux1 : (D.coord u).1 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.1
        have hvx0 : 0 ≤ (D.coord v).1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.1
        have hvx1 : (D.coord v).1 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.1
        exact ⟨onSide_bottom_of_coord D h00 h10 hux0 hux1 huv_y.1,
          onSide_bottom_of_coord D h00 h10 hvx0 hvx1 huv_y.2⟩)
  exact ⟨hatom, hbd⟩

lemma right_squareSideAtomic_atomicBoundary
    {c10 c11 a b : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1))
    (hside : s(a, b) ∈ sideAtomicEdges D c10 c11) :
    IsAtomicEdge D s(a, b) ∧ OnSquareBoundary D s(a, b) := by
  have h1011 : c10 ≠ c11 := by
    intro h
    have : ((1, 0) : ℝ × ℝ) = (1, 1) := by
      rw [← h10, h, h11]
    norm_num at this
  have hfront := right_segment_subset_frontier (D := D) h10 h11
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hbd : OnSquareBoundary D s(a, b) := by
    rw [onSquareBoundary_mk_iff]
    exact (segment_subset_of_onSide_local D hon.1 hon.2).trans hfront
  have hatom : IsAtomicEdge D s(a, b) :=
    isAtomic_of_mem_squareSideAtomicEdges (D := D) h1011 hside hfront
      (fun u v hu hv hmopen => by
        have hmSide :
            midpoint ℝ (D.coord a) (D.coord b) ∈
              segment ℝ (D.coord c10) (D.coord c11) :=
          segment_subset_of_onSide_local D hon.1 hon.2
            (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
        have hmr := hmSide
        rw [h10, h11, mem_segment_unit_right] at hmr
        have huv_x := openSegment_endpoints_on_right_of_mem_unitSquare hu hv hmopen hmr.1
        have huy0 : 0 ≤ (D.coord u).2 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.2
        have huy1 : (D.coord u).2 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.2
        have hvy0 : 0 ≤ (D.coord v).2 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.2
        have hvy1 : (D.coord v).2 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.2
        exact ⟨onSide_right_of_coord D h10 h11 huv_x.1 huy0 huy1,
          onSide_right_of_coord D h10 h11 huv_x.2 hvy0 hvy1⟩)
  exact ⟨hatom, hbd⟩

lemma top_squareSideAtomic_atomicBoundary
    {c11 c01 a b : D.vtx}
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (hside : s(a, b) ∈ sideAtomicEdges D c11 c01) :
    IsAtomicEdge D s(a, b) ∧ OnSquareBoundary D s(a, b) := by
  have h1101 : c11 ≠ c01 := by
    intro h
    have : ((1, 1) : ℝ × ℝ) = (0, 1) := by
      rw [← h11, h, h01]
    norm_num at this
  have hfront := top_segment_subset_frontier (D := D) h11 h01
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hbd : OnSquareBoundary D s(a, b) := by
    rw [onSquareBoundary_mk_iff]
    exact (segment_subset_of_onSide_local D hon.1 hon.2).trans hfront
  have hatom : IsAtomicEdge D s(a, b) :=
    isAtomic_of_mem_squareSideAtomicEdges (D := D) h1101 hside hfront
      (fun u v hu hv hmopen => by
        have hmSide :
            midpoint ℝ (D.coord a) (D.coord b) ∈
              segment ℝ (D.coord c11) (D.coord c01) :=
          segment_subset_of_onSide_local D hon.1 hon.2
            (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
        have hmt := hmSide
        rw [h11, h01, mem_segment_unit_top] at hmt
        have huv_y := openSegment_endpoints_on_top_of_mem_unitSquare hu hv hmopen hmt.2.2
        have hux0 : 0 ≤ (D.coord u).1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.1
        have hux1 : (D.coord u).1 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.1
        have hvx0 : 0 ≤ (D.coord v).1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.1
        have hvx1 : (D.coord v).1 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.1
        exact ⟨onSide_top_of_coord D h11 h01 hux0 hux1 huv_y.1,
          onSide_top_of_coord D h11 h01 hvx0 hvx1 huv_y.2⟩)
  exact ⟨hatom, hbd⟩

lemma left_squareSideAtomic_atomicBoundary
    {c01 c00 a b : D.vtx}
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0))
    (hside : s(a, b) ∈ sideAtomicEdges D c01 c00) :
    IsAtomicEdge D s(a, b) ∧ OnSquareBoundary D s(a, b) := by
  have h0100 : c01 ≠ c00 := by
    intro h
    have : ((0, 1) : ℝ × ℝ) = (0, 0) := by
      rw [← h01, h, h00]
    norm_num at this
  have hfront := left_segment_subset_frontier (D := D) h01 h00
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D hside
  have hbd : OnSquareBoundary D s(a, b) := by
    rw [onSquareBoundary_mk_iff]
    exact (segment_subset_of_onSide_local D hon.1 hon.2).trans hfront
  have hatom : IsAtomicEdge D s(a, b) :=
    isAtomic_of_mem_squareSideAtomicEdges (D := D) h0100 hside hfront
      (fun u v hu hv hmopen => by
        have hmSide :
            midpoint ℝ (D.coord a) (D.coord b) ∈
              segment ℝ (D.coord c01) (D.coord c00) :=
          segment_subset_of_onSide_local D hon.1 hon.2
            (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
        have hml := hmSide
        rw [h01, h00, mem_segment_unit_left] at hml
        have huv_x := openSegment_endpoints_on_left_of_mem_unitSquare hu hv hmopen hml.1
        have huy0 : 0 ≤ (D.coord u).2 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.1.2
        have huy1 : (D.coord u).2 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hu.2.2
        have hvy0 : 0 ≤ (D.coord v).2 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.1.2
        have hvy1 : (D.coord v).2 ≤ 1 := by
          simpa [unitSquareSetLocal, Set.mem_Icc, Prod.le_def] using hv.2.2
        exact ⟨onSide_left_of_coord D h01 h00 huv_x.1 huy0 huy1,
          onSide_left_of_coord D h01 h00 huv_x.2 hvy0 hvy1⟩)
  exact ⟨hatom, hbd⟩























open scoped Classical in
lemma squareBoundarySideAtomicList_RG_odd
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    Odd (listEdgeRGCount
      (squareBoundaryEdgeList
        (sideInteriorChain D c00 c10)
        (sideInteriorChain D c10 c11)
        (sideInteriorChain D c11 c01)
        (sideInteriorChain D c01 c00)
        c00 c10 c11 c01)
      (realTwoAdicColor ∘ D.coord)) := by
  classical
  refine squareBoundaryVertexChainRGCount_odd_of_side_colors
    (sideInteriorChain D c00 c10)
    (sideInteriorChain D c10 c11)
    (sideInteriorChain D c11 c01)
    (sideInteriorChain D c01 c00)
    c00 c10 c11 c01 (realTwoAdicColor ∘ D.coord)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [h00]
  · simp [h10]
  · simp [h11]
  · simp [h01]
  · intro v hv
    obtain ⟨x, hx⟩ := coord_bottom_of_onSide (D := D) h00 h10
      ((mem_sideInteriorChain_iff_local (D := D)).mp hv).1
    simpa [Function.comp_def, hx] using realTwoAdicColor_bottom_red_or_green x
  · intro v hv
    obtain ⟨y, hy⟩ := coord_right_of_onSide (D := D) h10 h11
      ((mem_sideInteriorChain_iff_local (D := D)).mp hv).1
    simpa [Function.comp_def, hy] using realTwoAdicColor_right_green_or_blue y
  · intro v hv
    obtain ⟨x, hx⟩ := coord_top_of_onSide (D := D) h11 h01
      ((mem_sideInteriorChain_iff_local (D := D)).mp hv).1
    simpa [Function.comp_def, hx] using realTwoAdicColor_top_green_or_blue x
  · intro v hv
    obtain ⟨y, hy⟩ := coord_left_of_onSide (D := D) h01 h00
      ((mem_sideInteriorChain_iff_local (D := D)).mp hv).1
    simpa [Function.comp_def, hy] using realTwoAdicColor_left_red_or_blue y



lemma squareBoundaryEdgeList_mem_atomicBoundary_of_square_corners
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    {e : Sym2 D.vtx}
    (he : e ∈ (squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01).toFinset) :
    IsAtomicEdge D e ∧ OnSquareBoundary D e := by
  classical
  induction e using Sym2.ind with
  | h a b =>
      have hlist :
          s(a, b) ∈ squareBoundaryEdgeList
            (sideInteriorChain D c00 c10)
            (sideInteriorChain D c10 c11)
            (sideInteriorChain D c11 c01)
            (sideInteriorChain D c01 c00)
            c00 c10 c11 c01 := by
        simpa using he
      have hcases :
          s(a, b) ∈ sideAtomicEdges D c00 c10 ∨
          s(a, b) ∈ sideAtomicEdges D c10 c11 ∨
          s(a, b) ∈ sideAtomicEdges D c11 c01 ∨
          s(a, b) ∈ sideAtomicEdges D c01 c00 := by
        simpa [squareBoundaryEdgeList, sideAtomicEdges, List.mem_append,
          List.append_assoc] using hlist
      rcases hcases with hbot | hright | htop | hleft
      · exact bottom_squareSideAtomic_atomicBoundary D h00 h10 hbot
      · exact right_squareSideAtomic_atomicBoundary D h10 h11 hright
      · exact top_squareSideAtomic_atomicBoundary D h11 h01 htop
      · exact left_squareSideAtomic_atomicBoundary D h01 h00 hleft

lemma atomicBoundary_iff_squareBoundaryEdgeList_of_square_corners
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (e : Sym2 D.vtx) :
    IsAtomicEdge D e ∧ OnSquareBoundary D e ↔
      e ∈ (squareBoundaryEdgeList
        (sideInteriorChain D c00 c10)
        (sideInteriorChain D c10 c11)
        (sideInteriorChain D c11 c01)
        (sideInteriorChain D c01 c00)
        c00 c10 c11 c01).toFinset := by
  constructor
  · exact atomicBoundary_mem_squareBoundaryEdgeList_of_square_corners
      (D := D) h00 h10 h11 h01
  · exact squareBoundaryEdgeList_mem_atomicBoundary_of_square_corners
      (D := D) h00 h10 h11 h01

open scoped Classical in
lemma atomicBoundaryRG_card_odd_of_squareBoundaryEdgeList
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (hboundary : ∀ e : Sym2 D.vtx,
      IsAtomicEdge D e ∧ OnSquareBoundary D e ↔
        e ∈ (squareBoundaryEdgeList
          (sideInteriorChain D c00 c10)
          (sideInteriorChain D c10 c11)
          (sideInteriorChain D c11 c01)
          (sideInteriorChain D c01 c00)
          c00 c10 c11 c01).toFinset) :
    Odd (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
        IsAtomicEdge D e ∧ OnSquareBoundary D e).card := by
  classical
  let L :=
    squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01
  have hset :
      (Finset.univ.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
          IsAtomicEdge D e ∧ OnSquareBoundary D e) =
      (L.toFinset.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1) := by
    ext e
    have hb' : IsAtomicEdge D e ∧ OnSquareBoundary D e ↔ e ∈ L := by
      rw [hboundary e]
      simp [L]
    by_cases hrg : edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1
    · simp [hrg, hb']
    · simp [hrg]
  have hnodup : L.Nodup := by
    simpa [L] using squareBoundaryEdgeList_nodup_of_square_corners
      (D := D) h00 h10 h11 h01
  have hcard :
      (L.toFinset.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1).card =
      listEdgeRGCount L (realTwoAdicColor ∘ D.coord) := by
    simpa [boundaryEdgeRedGreenCount, L] using
      boundaryEdgeRedGreenCount_toFinset L (realTwoAdicColor ∘ D.coord) hnodup
  have hoddList : Odd (listEdgeRGCount L (realTwoAdicColor ∘ D.coord)) := by
    simpa [L] using squareBoundarySideAtomicList_RG_odd
      (D := D) h00 h10 h11 h01
  rw [hset, hcard]
  exact hoddList

open scoped Classical in
theorem oddAtomicRG_card_odd :
    Odd (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
        Odd (atomicMult D e)).card := by
  classical
  obtain ⟨c00, c10, c11, c01, h00, h10, h11, h01⟩ :=
    exists_square_corners (D := D)
  rw [oddAtomicRG_filter_eq_atomicBoundaryRG (D := D)]
  exact atomicBoundaryRG_card_odd_of_squareBoundaryEdgeList
    (D := D) h00 h10 h11 h01
    (atomicBoundary_iff_squareBoundaryEdgeList_of_square_corners
      (D := D) h00 h10 h11 h01)

end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20DissectionEngine
import ProofsInTheBook.Chapter20Colors
import ProofsInTheBook.Chapter20AtomicCount
import ProofsInTheBook.Chapter20SideGeom
import ProofsInTheBook.Chapter20DissectionSperner
import ProofsInTheBook.Chapter20E2Boundary
-/
/- Source module: ProofsInTheBook.Chapter20DissectionFinal -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — final assembly

Wires the verified combinatorial layer to the geometric core (E2):
* per-side E3 bridge: along each subdivided triangle side the red-green atomic
  count has the parity of the side's endpoint colours (collinear ⇒ ≤2 colours);
* per-triangle: `listEdgeRGCount (triAtomicEdges i) ≡ triangleLocalRGCount` (mod 2);
* the atomic double-count + E2 turn the summed corner parity into the
  square-boundary atomic parity;
* the boundary organization (odd) + the Sperner spine close the chapter.

`monsky_dissection` is `False`-from-an-odd-equal-area-dissection, conditional only
on the geometric E2 (proved in the engine) and the boundary organization lemma.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable (D : SquareDissection)













end ProofsInTheBook.Chapter20

end


set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

theorem solution (hn : Odd D.n) : False := by
  refine monsky_false_of_odd_corner_parity hn
    (fun i => (D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2))
    D.equalArea ?_
  rw [Nat.odd_iff, sum_triangleLocalRGCount_mod_two_eq_oddAtomic D,
    ← Nat.odd_iff]
  exact oddAtomicRG_card_odd D
