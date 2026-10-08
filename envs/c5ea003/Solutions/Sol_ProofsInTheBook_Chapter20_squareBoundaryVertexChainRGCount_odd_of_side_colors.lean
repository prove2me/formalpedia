-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.squareBoundaryVertexChainRGCount_odd_of_side_colors
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:51:12.546005+00:00
-- url     : https://prove2.me/submissions/f9e501f4-3596-4cbb-bb48-c679fccb91c3

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20


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







































































































































theorem redGreenEdge_indicator_zmod_eq_bit_add {a b : MonskyColor}
    (ha : colorIsRedGreen a) (hb : colorIsRedGreen b) :
    ((if RedGreenEdge a b then 1 else 0 : ℕ) : ZMod 2) =
      colorRGParityBit a + colorRGParityBit b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem listRGTransitionCount_cons_append_zmod {a b : MonskyColor} (middle : List MonskyColor)
    (hcolors : ∀ c ∈ a :: middle ++ [b], colorIsRedGreen c) :
    (listRGTransitionCount (a :: middle ++ [b]) : ZMod 2) =
      colorRGParityBit a + colorRGParityBit b := by
  induction middle generalizing a with
  | nil =>
      have ha : colorIsRedGreen a := hcolors a (by simp)
      have hb : colorIsRedGreen b := hcolors b (by simp)
      simp [listRGTransitionCount, redGreenEdge_indicator_zmod_eq_bit_add ha hb]
  | cons x xs ih =>
      have ha : colorIsRedGreen a := hcolors a (by simp)
      have hx : colorIsRedGreen x := hcolors x (by simp)
      have htail : ∀ c ∈ x :: xs ++ [b], colorIsRedGreen c := by
        intro c hc
        exact hcolors c (List.mem_cons.mpr (Or.inr hc))
      have hfirst := redGreenEdge_indicator_zmod_eq_bit_add ha hx
      have htailcount := ih (a := x) htail
      simp only [List.cons_append] at htailcount
      simp only [List.cons_append, listRGTransitionCount]
      rw [Nat.cast_add, hfirst, htailcount]
      rcases hx with rfl | rfl <;> cases a <;> cases b <;> decide

theorem listRGTransitionCount_odd_of_red_to_green (middle : List MonskyColor)
    (hcolors : ∀ c ∈ red :: middle ++ [green], colorIsRedGreen c) :
    Odd (listRGTransitionCount (red :: middle ++ [green])) := by
  have h := listRGTransitionCount_cons_append_zmod (a := red) (b := green) middle hcolors
  simp [colorRGParityBit] at h
  exact ZMod.natCast_eq_one_iff_odd.mp h

theorem not_redGreenEdge_of_greenBlue {a b : MonskyColor}
    (ha : colorIsGreenBlue a) (hb : colorIsGreenBlue b) : ¬ RedGreenEdge a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem not_redGreenEdge_of_redBlue {a b : MonskyColor}
    (ha : colorIsRedBlue a) (hb : colorIsRedBlue b) : ¬ RedGreenEdge a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem listRGTransitionCount_eq_zero_of_greenBlue :
    ∀ l : List MonskyColor, (∀ c ∈ l, colorIsGreenBlue c) → listRGTransitionCount l = 0 := by
  intro l
  induction l with
  | nil => simp [listRGTransitionCount]
  | cons a tail ih =>
      intro h
      cases tail with
      | nil => simp [listRGTransitionCount]
      | cons b rest =>
          have ha : colorIsGreenBlue a := h a (by simp)
          have hb : colorIsGreenBlue b := h b (by simp)
          have htail : ∀ c ∈ b :: rest, colorIsGreenBlue c := by
            intro c hc
            exact h c (List.mem_cons.mpr (Or.inr hc))
          have hn : ¬ RedGreenEdge a b := not_redGreenEdge_of_greenBlue ha hb
          simp [listRGTransitionCount, hn, ih htail]

theorem listRGTransitionCount_eq_zero_of_redBlue :
    ∀ l : List MonskyColor, (∀ c ∈ l, colorIsRedBlue c) → listRGTransitionCount l = 0 := by
  intro l
  induction l with
  | nil => simp [listRGTransitionCount]
  | cons a tail ih =>
      intro h
      cases tail with
      | nil => simp [listRGTransitionCount]
      | cons b rest =>
          have ha : colorIsRedBlue a := h a (by simp)
          have hb : colorIsRedBlue b := h b (by simp)
          have htail : ∀ c ∈ b :: rest, colorIsRedBlue c := by
            intro c hc
            exact h c (List.mem_cons.mpr (Or.inr hc))
          have hn : ¬ RedGreenEdge a b := not_redGreenEdge_of_redBlue ha hb
          simp [listRGTransitionCount, hn, ih htail]

/--
Boundary-color parity for a square contour already split into four side chains.
This is the finite-color statement behind Monsky's boundary oddness.
-/
theorem squareBoundaryRGCount_odd_of_side_color_lists
    (bottom right top left : List MonskyColor)
    (hbottom : ∀ c ∈ red :: bottom ++ [green], colorIsRedGreen c)
    (hright : ∀ c ∈ green :: right ++ [green], colorIsGreenBlue c)
    (htop : ∀ c ∈ green :: top ++ [blue], colorIsGreenBlue c)
    (hleft : ∀ c ∈ blue :: left ++ [red], colorIsRedBlue c) :
    Odd (listRGTransitionCount (red :: bottom ++ [green]) +
      listRGTransitionCount (green :: right ++ [green]) +
      listRGTransitionCount (green :: top ++ [blue]) +
      listRGTransitionCount (blue :: left ++ [red])) := by
  have hbot := listRGTransitionCount_odd_of_red_to_green bottom hbottom
  have hright0 := listRGTransitionCount_eq_zero_of_greenBlue (green :: right ++ [green]) hright
  have htop0 := listRGTransitionCount_eq_zero_of_greenBlue (green :: top ++ [blue]) htop
  have hleft0 := listRGTransitionCount_eq_zero_of_redBlue (blue :: left ++ [red]) hleft
  rw [hright0, htop0, hleft0]
  simpa using hbot































@[simp]
theorem edgeRedGreen_mk {α : Type*} (color : α → MonskyColor) (a b : α) :
    edgeRedGreen color s(a, b) ↔ RedGreenEdge (color a) (color b) := by
  rfl



@[simp]
theorem edgeRGIndicator_mk {α : Type*} (color : α → MonskyColor) (a b : α) :
    edgeRGIndicator color s(a, b) =
      if RedGreenEdge (color a) (color b) then 1 else 0 := by
  classical
  by_cases h : RedGreenEdge (color a) (color b) <;> simp [edgeRGIndicator, h]























theorem consecutiveEdges_RGCount_eq_listRGTransitionCount_map {α : Type*}
    (vertices : List α) (color : α → MonskyColor) :
    listEdgeRGCount (consecutiveEdges vertices) color =
      listRGTransitionCount (vertices.map color) := by
  induction vertices with
  | nil => simp [consecutiveEdges, listEdgeRGCount, listRGTransitionCount]
  | cons a tail ih =>
      cases tail with
      | nil => simp [consecutiveEdges, listEdgeRGCount, listRGTransitionCount]
      | cons b rest =>
          have ih' : listEdgeRGCount (consecutiveEdges (b :: rest)) color =
              listRGTransitionCount (color b :: List.map color rest) := by
            simpa using ih
          simp only [List.map_cons, consecutiveEdges, listRGTransitionCount]
          rw [← ih']
          by_cases h : RedGreenEdge (color a) (color b)
          · simp [listEdgeRGCount, edgeRGIndicator_mk, h, Nat.add_comm]
          · simp [listEdgeRGCount, edgeRGIndicator_mk, h]

theorem listEdgeRGCount_append {α : Type*} (edges₁ edges₂ : List (Sym2 α))
    (color : α → MonskyColor) :
    listEdgeRGCount (edges₁ ++ edges₂) color =
      listEdgeRGCount edges₁ color + listEdgeRGCount edges₂ color := by
  simp [listEdgeRGCount, List.filter_append]





theorem squareBoundaryEdgeList_RGCount_eq {α : Type*}
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (color : α → MonskyColor) :
    listEdgeRGCount
        (squareBoundaryEdgeList bottom right top left bottomLeft bottomRight topRight topLeft)
        color =
      listRGTransitionCount ((bottomLeft :: bottom ++ [bottomRight]).map color) +
      listRGTransitionCount ((bottomRight :: right ++ [topRight]).map color) +
      listRGTransitionCount ((topRight :: top ++ [topLeft]).map color) +
      listRGTransitionCount ((topLeft :: left ++ [bottomLeft]).map color) := by
  simp [squareBoundaryEdgeList, listEdgeRGCount_append,
    consecutiveEdges_RGCount_eq_listRGTransitionCount_map, List.map_append]
  omega































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
open IsLocalRing
open MonskyColor

theorem solution {α : Type*}
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (color : α → MonskyColor)
    (hbottomLeft : color bottomLeft = red)
    (hbottomRight : color bottomRight = green)
    (htopRight : color topRight = green)
    (htopLeft : color topLeft = blue)
    (hbottom : ∀ v ∈ bottom, colorIsRedGreen (color v))
    (hright : ∀ v ∈ right, colorIsGreenBlue (color v))
    (htop : ∀ v ∈ top, colorIsGreenBlue (color v))
    (hleft : ∀ v ∈ left, colorIsRedBlue (color v)) :
    Odd (listEdgeRGCount
      (squareBoundaryEdgeList bottom right top left bottomLeft bottomRight topRight topLeft)
      color) := by
  rw [squareBoundaryEdgeList_RGCount_eq]
  have hbottomColors :
      ∀ c ∈ red :: (bottom.map color) ++ [green], colorIsRedGreen c := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with hfirst | hlast
    · rcases hfirst with hc | ⟨v, hv, hvc⟩
      · subst c
        exact Or.inl rfl
      · rw [← hvc]
        exact hbottom v hv
    · rcases hlast with hc | hnil
      · subst c
        exact Or.inr rfl
      · cases hnil
  have hrightColors :
      ∀ c ∈ green :: (right.map color) ++ [green], colorIsGreenBlue c := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with hfirst | hlast
    · rcases hfirst with hc | ⟨v, hv, hvc⟩
      · subst c
        exact Or.inl rfl
      · rw [← hvc]
        exact hright v hv
    · rcases hlast with hc | hnil
      · subst c
        exact Or.inl rfl
      · cases hnil
  have htopColors :
      ∀ c ∈ green :: (top.map color) ++ [blue], colorIsGreenBlue c := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with hfirst | hlast
    · rcases hfirst with hc | ⟨v, hv, hvc⟩
      · subst c
        exact Or.inl rfl
      · rw [← hvc]
        exact htop v hv
    · rcases hlast with hc | hnil
      · subst c
        exact Or.inr rfl
      · cases hnil
  have hleftColors :
      ∀ c ∈ blue :: (left.map color) ++ [red], colorIsRedBlue c := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with hfirst | hlast
    · rcases hfirst with hc | ⟨v, hv, hvc⟩
      · subst c
        exact Or.inr rfl
      · rw [← hvc]
        exact hleft v hv
    · rcases hlast with hc | hnil
      · subst c
        exact Or.inl rfl
      · cases hnil
  have hodd := squareBoundaryRGCount_odd_of_side_color_lists
    (bottom.map color) (right.map color) (top.map color) (left.map color)
    hbottomColors hrightColors htopColors hleftColors
  simpa [hbottomLeft, hbottomRight, htopRight, htopLeft, List.map_append] using hodd
