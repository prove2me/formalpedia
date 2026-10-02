-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.atomicBoundary_mem_squareBoundaryEdgeList_of_square_corners
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:50:53.902974+00:00
-- url     : https://prove2.me/submissions/b3554dfd-5f4f-4a18-9859-f178a7fa5c81

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























































theorem frontier_unitSquare :
    frontier (Set.Icc ((0, 0) : P) (1, 1)) =
      {p : P | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)} := by
  have hsquare :
      Set.Icc ((0, 0) : P) (1, 1) =
        Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp [Set.mem_Icc, Prod.le_def]
  rw [hsquare, frontier_prod_eq,
    frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  simp [closure_Icc]
  ext p
  simp [Set.mem_Icc]
  aesop



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
lemma mem_sideInteriorChain_iff_local {p q w : D.vtx} :
    w ∈ sideInteriorChain D p q ↔ OnSide D p q w ∧ w ≠ p ∧ w ≠ q := by
  classical
  unfold sideInteriorChain
  rw [List.mem_insertionSort, Finset.mem_toList]
  simp [OnSide]

open scoped Classical in
lemma sideInteriorChain_nodup_local (p q : D.vtx) :
    (sideInteriorChain D p q).Nodup := by
  classical
  unfold sideInteriorChain
  have hperm :
      ((Finset.univ.filter (fun w =>
          OnSide D p q w ∧ w ≠ p ∧ w ≠ q)).toList.insertionSort
        (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)).Perm
        (Finset.univ.filter (fun w =>
          OnSide D p q w ∧ w ≠ p ∧ w ≠ q)).toList :=
    List.perm_insertionSort _ _
  exact (List.Perm.nodup_iff hperm).mpr
    (Finset.nodup_toList (Finset.univ.filter (fun w =>
      OnSide D p q w ∧ w ≠ p ∧ w ≠ q)))

lemma left_not_mem_sideInteriorChain_local (p q : D.vtx) :
    p ∉ sideInteriorChain D p q := by
  intro hp
  exact (mem_sideInteriorChain_iff_local (D := D)).mp hp |>.2.1 rfl

lemma right_not_mem_sideInteriorChain_local (p q : D.vtx) :
    q ∉ sideInteriorChain D p q := by
  intro hq
  exact (mem_sideInteriorChain_iff_local (D := D)).mp hq |>.2.2 rfl

lemma sideChain_nodup_local {p q : D.vtx} (hpq : p ≠ q) :
    (p :: sideInteriorChain D p q ++ [q]).Nodup := by
  classical
  rw [List.nodup_append, List.nodup_cons]
  refine ⟨⟨left_not_mem_sideInteriorChain_local D p q,
    sideInteriorChain_nodup_local D p q⟩, List.nodup_singleton q, ?_⟩
  intro a ha b hb hab
  rw [List.mem_cons] at ha
  rw [List.mem_singleton] at hb
  subst b
  rcases ha with rfl | ha
  · exact hpq hab
  · exact right_not_mem_sideInteriorChain_local D p q (hab ▸ ha)

lemma endpoints_mem_of_mem_consecutiveEdges_local {α : Type*} {l : List α} {a b : α}
    (h : s(a, b) ∈ consecutiveEdges l) : a ∈ l ∧ b ∈ l := by
  induction l with
  | nil =>
      simp [consecutiveEdges] at h
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [consecutiveEdges] at h
      | cons y ys =>
          rw [consecutiveEdges, List.mem_cons] at h
          rcases h with h | h
          · rw [Sym2.eq_iff] at h
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          · have hh := ih h
            simp [hh.1, hh.2]



lemma not_diag_mem_consecutiveEdges_of_nodup_local {α : Type*} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) (a : α) :
    s(a, a) ∉ consecutiveEdges l := by
  induction l with
  | nil =>
      simp [consecutiveEdges]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [consecutiveEdges]
      | cons y ys =>
          rw [consecutiveEdges, List.mem_cons]
          rintro (h | h)
          · rw [Sym2.eq_iff] at h
            rcases h with ⟨hax, hay⟩ | ⟨hay, hax⟩
            · subst x
              subst y
              exact List.Nodup.notMem hnd (by simp)
            · subst x
              subst y
              exact List.Nodup.notMem hnd (by simp)
          · exact ih (List.Nodup.of_cons hnd) h

lemma ne_of_mk_mem_consecutiveEdges_of_nodup_local {α : Type*} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {a b : α}
    (h : s(a, b) ∈ consecutiveEdges l) : a ≠ b := by
  intro hab
  subst b
  exact not_diag_mem_consecutiveEdges_of_nodup_local hnd a h

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

lemma ne_of_mk_mem_sideAtomicEdges_local {p q a b : D.vtx} (hpq : p ≠ q)
    (h : s(a, b) ∈ sideAtomicEdges D p q) : a ≠ b := by
  unfold sideAtomicEdges at h
  exact ne_of_mk_mem_consecutiveEdges_of_nodup_local (sideChain_nodup_local D hpq) h



lemma sideParam_spec_of_onSide {p q w : D.vtx} (hpq : p ≠ q)
    (hw : OnSide D p q w) :
    sideParam D p q w ∈ Set.Icc (0 : ℝ) 1 ∧
      AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q w) = D.coord w := by
  unfold OnSide at hw
  obtain ⟨t, ht, htw⟩ := hw
  have hcoord_ne : D.coord q ≠ D.coord p := by
    intro h
    exact hpq (D.coord_inj h.symm)
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · have hparam : sideParam D p q w = t := by
      unfold sideParam
      rw [if_pos hx]
      have hxf := congrArg Prod.fst htw
      simp [AffineMap.lineMap_apply] at hxf
      field_simp [hx]
      linarith
    constructor
    · simpa [hparam] using ht
    · simpa [hparam] using htw
  · have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    have hparam : sideParam D p q w = t := by
      unfold sideParam
      rw [if_neg hx]
      have hyf := congrArg Prod.snd htw
      simp [AffineMap.lineMap_apply] at hyf
      field_simp [hy]
      linarith
    constructor
    · simpa [hparam] using ht
    · simpa [hparam] using htw

lemma sideParam_left_eq_local {p q : D.vtx} (hpq : p ≠ q) :
    sideParam D p q p = 0 := by
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · simp [hx]
  · have hcoord_ne : D.coord q ≠ D.coord p := by
      intro h
      exact hpq (D.coord_inj h.symm)
    have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    simp [hx]

lemma sideParam_right_eq_local {p q : D.vtx} (hpq : p ≠ q) :
    sideParam D p q q = 1 := by
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · rw [if_pos hx]
    field_simp [hx]
  · rw [if_neg hx]
    have hcoord_ne : D.coord q ≠ D.coord p := by
      intro h
      exact hpq (D.coord_inj h.symm)
    have hy : (D.coord q).2 ≠ (D.coord p).2 := by
      intro hy
      apply hcoord_ne
      ext <;> simp [not_not.mp hx, hy]
    field_simp [hy]

open scoped Classical in
lemma sideInteriorChain_pairwise_sideParam (p q : D.vtx) :
    List.Pairwise (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)
      (sideInteriorChain D p q) := by
  classical
  unfold sideInteriorChain
  exact List.pairwise_insertionSort _ _

open scoped Classical in
lemma sideChain_pairwise_sideParam {p q : D.vtx} (hpq : p ≠ q) :
    List.Pairwise (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)
      (p :: sideInteriorChain D p q ++ [q]) := by
  classical
  rw [List.pairwise_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.pairwise_cons]
    constructor
    · intro x hx
      rw [sideParam_left_eq_local (D := D) hpq]
      exact (sideParam_spec_of_onSide (D := D) hpq
        (sideInteriorChain_onSide_local D hx)).1.1
    · exact sideInteriorChain_pairwise_sideParam D p q
  · intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [hb, sideParam_right_eq_local (D := D) hpq]
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [sideParam_left_eq_local (D := D) hpq]
      norm_num
    · exact (sideParam_spec_of_onSide (D := D) hpq
        (sideInteriorChain_onSide_local D ha)).1.2

lemma not_sideParam_between_of_mem_consecutiveEdges_pairwise
    {α : Type*} {f : α → ℝ} :
    ∀ {l : List α} {a b w : α},
      List.Pairwise (fun x y => f x ≤ f y) l →
      s(a, b) ∈ consecutiveEdges l →
      w ∈ l →
      ¬ (f a < f w ∧ f w < f b)
  | [], a, b, w, _hpair, h, _hw => by
      simp [consecutiveEdges] at h
  | [_x], a, b, w, _hpair, h, _hw => by
      simp [consecutiveEdges] at h
  | x :: y :: rest, a, b, w, hpair, h, hw => by
      rw [List.pairwise_cons] at hpair
      have hxy0 : f x ≤ f y := hpair.1 y (by simp)
      rw [consecutiveEdges, List.mem_cons] at h
      rcases h with hfirst | htail
      · rw [Sym2.eq_iff] at hfirst
        rcases hfirst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [List.mem_cons] at hw
          intro hbetween
          rcases hw with rfl | hw
          · linarith
          · rw [List.mem_cons] at hw
            rcases hw with rfl | hwrest
            · linarith
            · have hyw : f b ≤ f w := by
                have htailPair := hpair.2
                rw [List.pairwise_cons] at htailPair
                exact htailPair.1 w hwrest
              linarith
        · intro hbetween
          linarith
      · rw [List.mem_cons] at hw
        rcases hw with rfl | hwtail
        · have hend := endpoints_mem_of_mem_consecutiveEdges_local htail
          have hxa : f w ≤ f a := hpair.1 a (by simpa using hend.1)
          intro hbetween
          linarith
        · exact not_sideParam_between_of_mem_consecutiveEdges_pairwise
            hpair.2 htail hwtail

lemma not_sideParam_between_of_mem_sideAtomicEdges {p q a b w : D.vtx}
    (hpq : p ≠ q) (h : s(a, b) ∈ sideAtomicEdges D p q)
    (hw : w ∈ p :: sideInteriorChain D p q ++ [q]) :
    ¬ (sideParam D p q a < sideParam D p q w ∧
      sideParam D p q w < sideParam D p q b) := by
  unfold sideAtomicEdges at h
  exact not_sideParam_between_of_mem_consecutiveEdges_pairwise
    (sideChain_pairwise_sideParam (D := D) hpq) h hw

lemma mem_consecutiveEdges_of_pairwise_no_between
    {α : Type*} {f : α → ℝ} {P : α → Prop} :
    ∀ {l : List α} {a b : α},
      l.Nodup →
      (∀ x, x ∈ l → P x) →
      (∀ x y, P x → P y → f x = f y → x = y) →
      l.Pairwise (fun x y => f x ≤ f y) →
      a ∈ l → b ∈ l → f a < f b →
      (∀ z, z ∈ l → ¬ (f a < f z ∧ f z < f b)) →
      s(a, b) ∈ consecutiveEdges l
  | [], a, b, _hnd, _hall, _hinj, _hpair, ha, _hb, _hlt, _hno => by
      simp at ha
  | x :: [], a, b, _hnd, _hall, _hinj, _hpair, ha, hb, hlt, _hno => by
      simp at ha hb
      subst a
      subst b
      linarith
  | x :: y :: ys, a, b, hnd, hall, hinj, hpair, ha, hb, hlt, hno => by
      rw [consecutiveEdges, List.mem_cons]
      rw [List.mem_cons] at ha hb
      have hpair' := List.pairwise_cons.mp hpair
      have hx_le_tail : ∀ t ∈ y :: ys, f x ≤ f t := hpair'.1
      have htail_pair : (y :: ys).Pairwise (fun x y => f x ≤ f y) := hpair'.2
      have htail_nd : (y :: ys).Nodup := List.Nodup.of_cons hnd
      have htail_all : ∀ z, z ∈ y :: ys → P z := by
        intro z hz
        exact hall z (by simp [hz])
      rcases ha with rfl | ha_tail
      · rcases hb with rfl | hb_tail
        · linarith
        · rw [List.mem_cons] at hb_tail
          rcases hb_tail with rfl | hb_ys
          · exact Or.inl rfl
          · have hxy_le : f a ≤ f y := hx_le_tail y (by simp)
            have hxy_ne : a ≠ y := by
              intro hxy
              exact (List.Nodup.notMem hnd) (by simp [hxy])
            have hxy_lt : f a < f y := by
              refine lt_of_le_of_ne hxy_le ?_
              intro heq
              exact hxy_ne (hinj a y (hall a (by simp)) (hall y (by simp)) heq)
            have hy_le_b : f y ≤ f b :=
              (List.pairwise_cons.mp htail_pair).1 b hb_ys
            have hy_ne_b : y ≠ b := by
              intro hyb
              subst b
              exact (List.Nodup.notMem htail_nd) hb_ys
            have hy_lt_b : f y < f b := by
              refine lt_of_le_of_ne hy_le_b ?_
              intro heq
              exact hy_ne_b (hinj y b (hall y (by simp))
                (hall b (by simp [hb_ys])) heq)
            exact False.elim (hno y (by simp) ⟨hxy_lt, hy_lt_b⟩)
      · rcases hb with rfl | hb_tail
        · have hx_le_a : f b ≤ f a := hx_le_tail a ha_tail
          exact False.elim (by linarith)
        · exact Or.inr
            (mem_consecutiveEdges_of_pairwise_no_between
              (l := y :: ys) (f := f) (P := P)
              htail_nd htail_all hinj htail_pair ha_tail hb_tail hlt
              (fun z hz => hno z (by simp [hz])))

lemma sideParam_injective_onSide_local {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b)
    (hparam : sideParam D p q a = sideParam D p q b) :
    a = b := by
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  apply D.coord_inj
  calc
    D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q a) :=
      ha_spec.2.symm
    _ = AffineMap.lineMap (D.coord p) (D.coord q) (sideParam D p q b) := by
      rw [hparam]
    _ = D.coord b := hb_spec.2

lemma sideParam_eq_of_lineMap_local {p q w : D.vtx} (hpq : p ≠ q) {t : ℝ}
    (hw : D.coord w = AffineMap.lineMap (D.coord p) (D.coord q) t) :
    sideParam D p q w = t := by
  have hcoord_ne : D.coord q ≠ D.coord p := by
    intro h
    exact hpq (D.coord_inj h.symm)
  unfold sideParam
  by_cases hx : (D.coord q).1 ≠ (D.coord p).1
  · simp [hx]
    have hfst := congrArg Prod.fst hw
    simp [AffineMap.lineMap_apply] at hfst
    field_simp [hx]
    linarith
  · simp [hx]
    have hxeq : (D.coord q).1 = (D.coord p).1 := by exact not_not.mp hx
    have hy : (D.coord q).2 - (D.coord p).2 ≠ 0 := by
      intro hzero
      apply hcoord_ne
      ext
      · exact hxeq
      · linarith
    have hsnd := congrArg Prod.snd hw
    simp [AffineMap.lineMap_apply] at hsnd
    field_simp [hy]
    linarith





lemma mem_sideChain_of_onSide_local {p q w : D.vtx}
    (hw : OnSide D p q w) :
    w ∈ p :: sideInteriorChain D p q ++ [q] := by
  by_cases hwp : w = p
  · simp [hwp]
  by_cases hwq : w = q
  · simp [hwq]
  have hwint : w ∈ sideInteriorChain D p q := by
    rw [mem_sideInteriorChain_iff_local]
    exact ⟨hw, hwp, hwq⟩
  simp [hwint]

lemma lineMap_lineMap_param (P Q : ℝ × ℝ) (ta tb r : ℝ) :
    AffineMap.lineMap
        (AffineMap.lineMap P Q ta) (AffineMap.lineMap P Q tb) r =
      AffineMap.lineMap P Q ((1 - r) * ta + r * tb) := by
  ext <;> simp [AffineMap.lineMap_apply] <;> ring

lemma sbtw_of_sideParam_between_local {p q a b z : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hz : OnSide D p q z)
    (haz : sideParam D p q a < sideParam D p q z)
    (hzb : sideParam D p q z < sideParam D p q b) :
    Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  let ta := sideParam D p q a
  let tz := sideParam D p q z
  let tb := sideParam D p q b
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hz_spec := sideParam_spec_of_onSide (D := D) hpq hz
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  have hden : tb - ta ≠ 0 := by
    dsimp [ta, tb]
    linarith
  have hden_pos : 0 < tb - ta := by
    dsimp [ta, tb]
    linarith
  have hnumer_pos : 0 < tz - ta := by
    dsimp [ta, tz]
    linarith
  let r : ℝ := (tz - ta) / (tb - ta)
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [r, ta, tz, tb]
      exact div_pos hnumer_pos hden_pos
    · dsimp [r, ta, tz, tb]
      rw [div_lt_one (sub_pos.mpr (by simpa [ta, tz, tb] using haz.trans hzb))]
      linarith
  rw [sbtw_iff_mem_image_Ioo_and_ne]
  constructor
  · refine ⟨r, hr, ?_⟩
    calc
      AffineMap.lineMap (D.coord a) (D.coord b) r
          = AffineMap.lineMap
              (AffineMap.lineMap (D.coord p) (D.coord q) ta)
              (AffineMap.lineMap (D.coord p) (D.coord q) tb) r := by
              rw [ha_spec.2, hb_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * ta + r * tb) := by
              rw [lineMap_lineMap_param]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) tz := by
              congr 1
              dsimp [r]
              field_simp [hden]
              ring
      _ = D.coord z := hz_spec.2
  · intro hab
    have habv : a = b := D.coord_inj hab
    subst b
    linarith

lemma sideParam_between_of_sbtw_local {p q a b z : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hz : OnSide D p q z)
    (hs : Sbtw ℝ (D.coord a) (D.coord z) (D.coord b)) :
    (sideParam D p q a < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q b) ∨
      (sideParam D p q b < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q a) := by
  let ta := sideParam D p q a
  let tz := sideParam D p q z
  let tb := sideParam D p q b
  have ha_spec := sideParam_spec_of_onSide (D := D) hpq ha
  have hz_spec := sideParam_spec_of_onSide (D := D) hpq hz
  have hb_spec := sideParam_spec_of_onSide (D := D) hpq hb
  rcases hs.mem_image_Ioo with ⟨r, hr, hzr⟩
  have hz_param : tz = (1 - r) * ta + r * tb := by
    dsimp [tz]
    apply sideParam_eq_of_lineMap_local D hpq
    calc
      D.coord z = AffineMap.lineMap (D.coord a) (D.coord b) r := hzr.symm
      _ = AffineMap.lineMap
            (AffineMap.lineMap (D.coord p) (D.coord q) ta)
            (AffineMap.lineMap (D.coord p) (D.coord q) tb) r := by
            rw [ha_spec.2, hb_spec.2]
      _ = AffineMap.lineMap (D.coord p) (D.coord q) ((1 - r) * ta + r * tb) := by
            rw [lineMap_lineMap_param]
  have hne_param : ta ≠ tb := by
    intro htab
    have hcoord : D.coord a = D.coord b := by
      calc
        D.coord a = AffineMap.lineMap (D.coord p) (D.coord q) ta := ha_spec.2.symm
        _ = AffineMap.lineMap (D.coord p) (D.coord q) tb := by rw [htab]
        _ = D.coord b := hb_spec.2
    exact hs.left_ne_right hcoord
  rcases lt_or_gt_of_ne hne_param with hlt | hgt
  · left
    change ta < tz ∧ tz < tb
    rw [hz_param]
    constructor <;> nlinarith [hr.1, hr.2, hlt]
  · right
    change tb < tz ∧ tz < ta
    rw [hz_param]
    constructor <;> nlinarith [hr.1, hr.2, hgt]

lemma mem_sideAtomicEdges_of_onSide_no_sideParam_between
    {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b)
    (hlt : sideParam D p q a < sideParam D p q b)
    (hno : ∀ z : D.vtx, OnSide D p q z →
      ¬ (sideParam D p q a < sideParam D p q z ∧
        sideParam D p q z < sideParam D p q b)) :
    s(a, b) ∈ sideAtomicEdges D p q := by
  let chain := p :: sideInteriorChain D p q ++ [q]
  have ha_mem : a ∈ chain := mem_sideChain_of_onSide_local (D := D) ha
  have hb_mem : b ∈ chain := mem_sideChain_of_onSide_local (D := D) hb
  have hall : ∀ x, x ∈ chain → OnSide D p q x := by
    intro x hx
    exact onSide_of_mem_sideChain_local D hx
  unfold sideAtomicEdges
  exact mem_consecutiveEdges_of_pairwise_no_between
    (l := chain) (f := sideParam D p q) (P := fun x => OnSide D p q x)
    (sideChain_nodup_local D hpq) hall
    (fun x y hx hy hxy => sideParam_injective_onSide_local D hpq hx hy hxy)
    (sideChain_pairwise_sideParam (D := D) hpq) ha_mem hb_mem hlt
    (fun z hz => hno z (hall z hz))

lemma mem_sideAtomicEdges_of_onSide_no_sbtw
    {p q a b : D.vtx} (hpq : p ≠ q)
    (ha : OnSide D p q a) (hb : OnSide D p q b) (hab : a ≠ b)
    (hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b)) :
    s(a, b) ∈ sideAtomicEdges D p q := by
  have hparam_ne : sideParam D p q a ≠ sideParam D p q b := by
    intro hparam
    exact hab (sideParam_injective_onSide_local D hpq ha hb hparam)
  rcases lt_or_gt_of_ne hparam_ne with hlt | hgt
  · exact mem_sideAtomicEdges_of_onSide_no_sideParam_between (D := D) hpq ha hb hlt
      (fun z hz hbetween =>
        hno z (sbtw_of_sideParam_between_local (D := D) hpq ha hb hz hbetween.1 hbetween.2))
  · have hmem : s(b, a) ∈ sideAtomicEdges D p q :=
      mem_sideAtomicEdges_of_onSide_no_sideParam_between (D := D) hpq hb ha hgt
        (fun z hz hbetween =>
          hno z ((sbtw_of_sideParam_between_local (D := D) hpq hb ha hz
            hbetween.1 hbetween.2).symm))
    simpa [Sym2.eq_swap] using hmem

lemma segment_subset_of_onSide_local {p q a b : D.vtx}
    (ha : OnSide D p q a) (hb : OnSide D p q b) :
    segment ℝ (D.coord a) (D.coord b) ⊆ segment ℝ (D.coord p) (D.coord q) := by
  exact (convex_segment (D.coord p) (D.coord q)).segment_subset
    (Wbtw.mem_segment ha) (Wbtw.mem_segment hb)

lemma not_sbtw_of_mem_sideAtomicEdges {p q a b z : D.vtx} (hpq : p ≠ q)
    (h : s(a, b) ∈ sideAtomicEdges D p q) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  intro hs
  have hmem :
      s(a, b) ∈ consecutiveEdges (p :: sideInteriorChain D p q ++ [q]) := by
    simpa [sideAtomicEdges] using h
  have hon := endpoints_onSide_of_mem_sideAtomicEdges_local D h
  have hzseg :
      D.coord z ∈ segment ℝ (D.coord p) (D.coord q) :=
    segment_subset_of_onSide_local D hon.1 hon.2 hs.wbtw.mem_segment
  have hzon : OnSide D p q z := (mem_segment_iff_wbtw (R := ℝ)).mp hzseg
  have hzmem : z ∈ p :: sideInteriorChain D p q ++ [q] :=
    mem_sideChain_of_onSide_local (D := D) hzon
  rcases sideParam_between_of_sbtw_local (D := D) hpq hon.1 hon.2 hzon hs with hbetween | hbetween
  · exact not_sideParam_between_of_mem_sideAtomicEdges D hpq h hzmem hbetween
  · have hswap : s(b, a) ∈ sideAtomicEdges D p q := by
      simpa [Sym2.eq_swap] using h
    exact not_sideParam_between_of_mem_sideAtomicEdges D hpq hswap hzmem hbetween



lemma mem_triAtomicEdges_iff_local {i : Fin D.n} {e : Sym2 D.vtx} :
    e ∈ triAtomicEdges D i ↔
      e ∈ sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 ∨
      e ∈ sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2 ∨
      e ∈ sideAtomicEdges D (D.tri i).2.2 (D.tri i).1 := by
  simp [triAtomicEdges, or_assoc]

lemma tri_v₁_ne_v₂_local (i : Fin D.n) : (D.tri i).1 ≠ (D.tri i).2.1 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma tri_v₂_ne_v₃_local (i : Fin D.n) : (D.tri i).2.1 ≠ (D.tri i).2.2 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma tri_v₃_ne_v₁_local (i : Fin D.n) : (D.tri i).2.2 ≠ (D.tri i).1 := by
  intro h
  apply D.nondeg i
  simpa [h, doubleArea]

lemma not_sbtw_of_mem_triAtomicEdges {i : Fin D.n} {a b z : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  rw [mem_triAtomicEdges_iff_local] at h
  rcases h with h | h | h
  · exact not_sbtw_of_mem_sideAtomicEdges D (tri_v₁_ne_v₂_local D i) h
  · exact not_sbtw_of_mem_sideAtomicEdges D (tri_v₂_ne_v₃_local D i) h
  · exact not_sbtw_of_mem_sideAtomicEdges D (tri_v₃_ne_v₁_local D i) h

lemma not_sbtw_of_isAtomicEdge_mk {a b z : D.vtx}
    (he : IsAtomicEdge D s(a, b)) :
    ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) := by
  rcases he with ⟨i, hi⟩
  exact not_sbtw_of_mem_triAtomicEdges D hi









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

lemma mem_segment_unit_top (p : ℝ × ℝ) :
    p ∈ segment ℝ ((1, 1) : ℝ × ℝ) (0, 1) ↔
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · simp [Prod.smul_mk, Prod.mk_add_mk]
      linarith [ht.2]
    · constructor
      · simp [Prod.smul_mk, Prod.mk_add_mk]
        linarith [ht.1]
      · simp [Prod.smul_mk, Prod.mk_add_mk]
  · intro hp
    refine ⟨1 - p.1, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · ext <;> simp [AffineMap.lineMap_apply, hp.2.2] <;> ring

lemma mem_segment_unit_left (p : ℝ × ℝ) :
    p ∈ segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) ↔
      p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · simp [Prod.smul_mk, Prod.mk_add_mk]
    · constructor
      · simp [Prod.smul_mk, Prod.mk_add_mk]
        linarith [ht.2]
      · simp [Prod.smul_mk, Prod.mk_add_mk]
        linarith [ht.1]
  · intro hp
    refine ⟨1 - p.2, ⟨?_, ?_⟩, ?_⟩
    · linarith
    · linarith
    · ext <;> simp [AffineMap.lineMap_apply, hp.1] <;> ring

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









lemma onSquareBoundary_mk_iff {a b : D.vtx} :
    OnSquareBoundary D s(a, b) ↔
      segment ℝ (D.coord a) (D.coord b) ⊆
        frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) := by
  rfl

























lemma ne_of_mem_triAtomicEdges_local {i : Fin D.n} {a b : D.vtx}
    (h : s(a, b) ∈ triAtomicEdges D i) : a ≠ b := by
  rw [mem_triAtomicEdges_iff_local] at h
  rcases h with h | h | h
  · exact ne_of_mk_mem_sideAtomicEdges_local D (tri_v₁_ne_v₂_local D i) h
  · exact ne_of_mk_mem_sideAtomicEdges_local D (tri_v₂_ne_v₃_local D i) h
  · exact ne_of_mk_mem_sideAtomicEdges_local D (tri_v₃_ne_v₁_local D i) h

lemma ne_of_isAtomicEdge_mk {a b : D.vtx}
    (he : IsAtomicEdge D s(a, b)) : a ≠ b := by
  rcases he with ⟨i, hi⟩
  exact ne_of_mem_triAtomicEdges_local D hi

lemma square_side_cases_of_segment_subset_frontier
    {c00 c10 c11 c01 a b : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (hseg : segment ℝ (D.coord a) (D.coord b) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1))) :
    (OnSide D c00 c10 a ∧ OnSide D c00 c10 b) ∨
      (OnSide D c10 c11 a ∧ OnSide D c10 c11 b) ∨
      (OnSide D c11 c01 a ∧ OnSide D c11 c01 b) ∨
      (OnSide D c01 c00 a ∧ OnSide D c01 c00 b) := by
  let m := midpoint ℝ (D.coord a) (D.coord b)
  have haFront := hseg (left_mem_segment ℝ (D.coord a) (D.coord b))
  have hbFront := hseg (right_mem_segment ℝ (D.coord a) (D.coord b))
  have hmFront := hseg (midpoint_mem_segment (𝕜 := ℝ) (D.coord a) (D.coord b))
  rw [frontier_unitSquare] at haFront hbFront hmFront
  rcases haFront with ⟨ha0x, ha1x, ha0y, ha1y, _⟩
  rcases hbFront with ⟨hb0x, hb1x, hb0y, hb1y, _⟩
  rcases hmFront with ⟨_hm0x, _hm1x, _hm0y, _hm1y, hmcase⟩
  rcases hmcase with hm0x | hm1x | hm0y | hm1y
  · have hsum : (D.coord a).1 + (D.coord b).1 = 0 := by
      have h := hm0x
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have ha_x : (D.coord a).1 = 0 := by linarith [ha0x, hb0x, hsum]
    have hb_x : (D.coord b).1 = 0 := by linarith [ha0x, hb0x, hsum]
    exact Or.inr <| Or.inr <| Or.inr
      ⟨onSide_left_of_coord D h01 h00 ha_x ha0y ha1y,
        onSide_left_of_coord D h01 h00 hb_x hb0y hb1y⟩
  · have hsum : (D.coord a).1 + (D.coord b).1 = 2 := by
      have h := hm1x
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have ha_x : (D.coord a).1 = 1 := by linarith [ha1x, hb1x, hsum]
    have hb_x : (D.coord b).1 = 1 := by linarith [ha1x, hb1x, hsum]
    exact Or.inr <| Or.inl
      ⟨onSide_right_of_coord D h10 h11 ha_x ha0y ha1y,
        onSide_right_of_coord D h10 h11 hb_x hb0y hb1y⟩
  · have hsum : (D.coord a).2 + (D.coord b).2 = 0 := by
      have h := hm0y
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have ha_y : (D.coord a).2 = 0 := by linarith [ha0y, hb0y, hsum]
    have hb_y : (D.coord b).2 = 0 := by linarith [ha0y, hb0y, hsum]
    exact Or.inl
      ⟨onSide_bottom_of_coord D h00 h10 ha0x ha1x ha_y,
        onSide_bottom_of_coord D h00 h10 hb0x hb1x hb_y⟩
  · have hsum : (D.coord a).2 + (D.coord b).2 = 2 := by
      have h := hm1y
      simp [m, midpoint, AffineMap.lineMap_apply, invOf_eq_inv] at h
      linarith
    have ha_y : (D.coord a).2 = 1 := by linarith [ha1y, hb1y, hsum]
    have hb_y : (D.coord b).2 = 1 := by linarith [ha1y, hb1y, hsum]
    exact Or.inr <| Or.inr <| Or.inl
      ⟨onSide_top_of_coord D h11 h01 ha0x ha1x ha_y,
        onSide_top_of_coord D h11 h01 hb0x hb1x hb_y⟩

lemma square_corner_ne {a b : D.vtx} {pa pb : ℝ × ℝ}
    (ha : D.coord a = pa) (hb : D.coord b = pb) (hp : pa ≠ pb) : a ≠ b := by
  intro h
  apply hp
  calc
    pa = D.coord a := ha.symm
    _ = D.coord b := by rw [h]
    _ = pb := hb



























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

lemma solution
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    {e : Sym2 D.vtx}
    (he : IsAtomicEdge D e ∧ OnSquareBoundary D e) :
    e ∈ (squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01).toFinset := by
  classical
  induction e using Sym2.ind with
  | h a b =>
      have h0010 : c00 ≠ c10 := square_corner_ne D h00 h10 (by norm_num)
      have h1011 : c10 ≠ c11 := square_corner_ne D h10 h11 (by norm_num)
      have h1101 : c11 ≠ c01 := square_corner_ne D h11 h01 (by norm_num)
      have h0100 : c01 ≠ c00 := square_corner_ne D h01 h00 (by norm_num)
      have hab : a ≠ b := ne_of_isAtomicEdge_mk D he.1
      have hno : ∀ z : D.vtx, ¬ Sbtw ℝ (D.coord a) (D.coord z) (D.coord b) :=
        fun z => not_sbtw_of_isAtomicEdge_mk D he.1
      have hseg :
          segment ℝ (D.coord a) (D.coord b) ⊆
            frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) :=
        (onSquareBoundary_mk_iff (D := D)).mp he.2
      rcases square_side_cases_of_segment_subset_frontier
          (D := D) h00 h10 h11 h01 hseg with hbot | hrest
      · have hmem : s(a, b) ∈ sideAtomicEdges D c00 c10 :=
          mem_sideAtomicEdges_of_onSide_no_sbtw D h0010 hbot.1 hbot.2 hab hno
        have hlist :
            s(a, b) ∈ squareBoundaryEdgeList
              (sideInteriorChain D c00 c10)
              (sideInteriorChain D c10 c11)
              (sideInteriorChain D c11 c01)
              (sideInteriorChain D c01 c00)
              c00 c10 c11 c01 := by
          have hmem' :
              s(a, b) ∈ consecutiveEdges
                (c00 :: sideInteriorChain D c00 c10 ++ [c10]) := by
            simpa [sideAtomicEdges] using hmem
          simpa [squareBoundaryEdgeList, List.mem_append] using
            (Or.inl hmem' :
              s(a, b) ∈ consecutiveEdges
                (c00 :: sideInteriorChain D c00 c10 ++ [c10]) ∨
              s(a, b) ∈ consecutiveEdges
                (c10 :: sideInteriorChain D c10 c11 ++ [c11]) ∨
              s(a, b) ∈ consecutiveEdges
                (c11 :: sideInteriorChain D c11 c01 ++ [c01]) ∨
              s(a, b) ∈ consecutiveEdges
                (c01 :: sideInteriorChain D c01 c00 ++ [c00]))
        simpa using hlist
      · rcases hrest with hrightSide | hrest
        · have hmem : s(a, b) ∈ sideAtomicEdges D c10 c11 :=
            mem_sideAtomicEdges_of_onSide_no_sbtw D h1011 hrightSide.1 hrightSide.2 hab hno
          have hlist :
              s(a, b) ∈ squareBoundaryEdgeList
                (sideInteriorChain D c00 c10)
                (sideInteriorChain D c10 c11)
                (sideInteriorChain D c11 c01)
                (sideInteriorChain D c01 c00)
                c00 c10 c11 c01 := by
            have hmem' :
                s(a, b) ∈ consecutiveEdges
                  (c10 :: sideInteriorChain D c10 c11 ++ [c11]) := by
              simpa [sideAtomicEdges] using hmem
            simpa [squareBoundaryEdgeList, List.mem_append] using
              (Or.inr <| Or.inl hmem' :
                s(a, b) ∈ consecutiveEdges
                  (c00 :: sideInteriorChain D c00 c10 ++ [c10]) ∨
                s(a, b) ∈ consecutiveEdges
                  (c10 :: sideInteriorChain D c10 c11 ++ [c11]) ∨
                s(a, b) ∈ consecutiveEdges
                  (c11 :: sideInteriorChain D c11 c01 ++ [c01]) ∨
                s(a, b) ∈ consecutiveEdges
                  (c01 :: sideInteriorChain D c01 c00 ++ [c00]))
          simpa using hlist
        · rcases hrest with htopSide | hleftSide
          · have hmem : s(a, b) ∈ sideAtomicEdges D c11 c01 :=
              mem_sideAtomicEdges_of_onSide_no_sbtw D h1101 htopSide.1 htopSide.2 hab hno
            have hlist :
                s(a, b) ∈ squareBoundaryEdgeList
                  (sideInteriorChain D c00 c10)
                  (sideInteriorChain D c10 c11)
                  (sideInteriorChain D c11 c01)
                  (sideInteriorChain D c01 c00)
                  c00 c10 c11 c01 := by
              have hmem' :
                  s(a, b) ∈ consecutiveEdges
                    (c11 :: sideInteriorChain D c11 c01 ++ [c01]) := by
                simpa [sideAtomicEdges] using hmem
              simpa [squareBoundaryEdgeList, List.mem_append] using
                (Or.inr <| Or.inr <| Or.inl hmem' :
                  s(a, b) ∈ consecutiveEdges
                    (c00 :: sideInteriorChain D c00 c10 ++ [c10]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c10 :: sideInteriorChain D c10 c11 ++ [c11]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c11 :: sideInteriorChain D c11 c01 ++ [c01]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c01 :: sideInteriorChain D c01 c00 ++ [c00]))
            simpa using hlist
          · have hmem : s(a, b) ∈ sideAtomicEdges D c01 c00 :=
              mem_sideAtomicEdges_of_onSide_no_sbtw D h0100 hleftSide.1 hleftSide.2 hab hno
            have hlist :
                s(a, b) ∈ squareBoundaryEdgeList
                  (sideInteriorChain D c00 c10)
                  (sideInteriorChain D c10 c11)
                  (sideInteriorChain D c11 c01)
                  (sideInteriorChain D c01 c00)
                  c00 c10 c11 c01 := by
              have hmem' :
                  s(a, b) ∈ consecutiveEdges
                    (c01 :: sideInteriorChain D c01 c00 ++ [c00]) := by
                simpa [sideAtomicEdges] using hmem
              simpa [squareBoundaryEdgeList, List.mem_append] using
                (Or.inr <| Or.inr <| Or.inr hmem' :
                  s(a, b) ∈ consecutiveEdges
                    (c00 :: sideInteriorChain D c00 c10 ++ [c10]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c10 :: sideInteriorChain D c10 c11 ++ [c11]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c11 :: sideInteriorChain D c11 c01 ++ [c01]) ∨
                  s(a, b) ∈ consecutiveEdges
                    (c01 :: sideInteriorChain D c01 c00 ++ [c00]))
            simpa using hlist
