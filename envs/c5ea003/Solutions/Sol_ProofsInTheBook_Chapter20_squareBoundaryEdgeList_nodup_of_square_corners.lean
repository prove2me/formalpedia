-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.squareBoundaryEdgeList_nodup_of_square_corners
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:51:10.490863+00:00
-- url     : https://prove2.me/submissions/8425ca5f-b9e3-459d-bdf3-d57472e88ebd

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

lemma consecutiveEdges_nodup_of_nodup_local {α : Type*} [DecidableEq α] :
    ∀ {l : List α}, l.Nodup → (consecutiveEdges l).Nodup
  | [], _ => by simp [consecutiveEdges]
  | [_], _ => by simp [consecutiveEdges]
  | a :: b :: rest, h => by
      rw [consecutiveEdges, List.nodup_cons]
      refine ⟨?_, consecutiveEdges_nodup_of_nodup_local (List.Nodup.of_cons h)⟩
      intro hmem
      have hend := endpoints_mem_of_mem_consecutiveEdges_local (l := b :: rest) hmem
      exact List.Nodup.notMem h hend.1

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

lemma sideAtomicEdges_nodup_local {p q : D.vtx} (hpq : p ≠ q) :
    (sideAtomicEdges D p q).Nodup := by
  unfold sideAtomicEdges
  exact consecutiveEdges_nodup_of_nodup_local (sideChain_nodup_local D hpq)























































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

























































lemma square_corner_ne {a b : D.vtx} {pa pb : ℝ × ℝ}
    (ha : D.coord a = pa) (hb : D.coord b = pb) (hp : pa ≠ pb) : a ≠ b := by
  intro h
  apply hp
  calc
    pa = D.coord a := ha.symm
    _ = D.coord b := by rw [h]
    _ = pb := hb

lemma bottom_right_sideAtomicEdges_disjoint
    {c00 c10 c11 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h0010 : c00 ≠ c10) :
    (sideAtomicEdges D c00 c10).Disjoint (sideAtomicEdges D c10 c11) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D h0010 he₁
      have hb := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have hr := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨xa, hxa⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.1
      obtain ⟨ya, hya⟩ := coord_right_of_onSide (D := D) h10 h11 hr.1
      obtain ⟨xb, hxb⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.2
      obtain ⟨yb, hyb⟩ := coord_right_of_onSide (D := D) h10 h11 hr.2
      have hacoord : D.coord a = (1, 0) := by
        ext
        · simpa using congrArg Prod.fst hya
        · simpa using congrArg Prod.snd hxa
      have hbcoord : D.coord b = (1, 0) := by
        ext
        · simpa using congrArg Prod.fst hyb
        · simpa using congrArg Prod.snd hxb
      exact hne (D.coord_inj (hacoord.trans hbcoord.symm))

lemma right_top_sideAtomicEdges_disjoint
    {c10 c11 c01 : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1))
    (h01 : D.coord c01 = (0, 1)) (h1011 : c10 ≠ c11) :
    (sideAtomicEdges D c10 c11).Disjoint (sideAtomicEdges D c11 c01) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D h1011 he₁
      have hr := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have ht := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨ya, hya⟩ := coord_right_of_onSide (D := D) h10 h11 hr.1
      obtain ⟨xa, hxa⟩ := coord_top_of_onSide (D := D) h11 h01 ht.1
      obtain ⟨yb, hyb⟩ := coord_right_of_onSide (D := D) h10 h11 hr.2
      obtain ⟨xb, hxb⟩ := coord_top_of_onSide (D := D) h11 h01 ht.2
      have hacoord : D.coord a = (1, 1) := by
        ext
        · simpa using congrArg Prod.fst hya
        · simpa using congrArg Prod.snd hxa
      have hbcoord : D.coord b = (1, 1) := by
        ext
        · simpa using congrArg Prod.fst hyb
        · simpa using congrArg Prod.snd hxb
      exact hne (D.coord_inj (hacoord.trans hbcoord.symm))

lemma top_left_sideAtomicEdges_disjoint
    {c11 c01 c00 : D.vtx}
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1))
    (h00 : D.coord c00 = (0, 0)) (h1101 : c11 ≠ c01) :
    (sideAtomicEdges D c11 c01).Disjoint (sideAtomicEdges D c01 c00) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D h1101 he₁
      have ht := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have hl := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨xa, hxa⟩ := coord_top_of_onSide (D := D) h11 h01 ht.1
      obtain ⟨ya, hya⟩ := coord_left_of_onSide (D := D) h01 h00 hl.1
      obtain ⟨xb, hxb⟩ := coord_top_of_onSide (D := D) h11 h01 ht.2
      obtain ⟨yb, hyb⟩ := coord_left_of_onSide (D := D) h01 h00 hl.2
      have hacoord : D.coord a = (0, 1) := by
        ext
        · simpa using congrArg Prod.fst hya
        · simpa using congrArg Prod.snd hxa
      have hbcoord : D.coord b = (0, 1) := by
        ext
        · simpa using congrArg Prod.fst hyb
        · simpa using congrArg Prod.snd hxb
      exact hne (D.coord_inj (hacoord.trans hbcoord.symm))

lemma left_bottom_sideAtomicEdges_disjoint
    {c01 c00 c10 : D.vtx}
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0))
    (h10 : D.coord c10 = (1, 0)) (h0100 : c01 ≠ c00) :
    (sideAtomicEdges D c01 c00).Disjoint (sideAtomicEdges D c00 c10) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hne : a ≠ b := ne_of_mk_mem_sideAtomicEdges_local D h0100 he₁
      have hl := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have hb := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨ya, hya⟩ := coord_left_of_onSide (D := D) h01 h00 hl.1
      obtain ⟨xa, hxa⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.1
      obtain ⟨yb, hyb⟩ := coord_left_of_onSide (D := D) h01 h00 hl.2
      obtain ⟨xb, hxb⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.2
      have hacoord : D.coord a = (0, 0) := by
        ext
        · simpa using congrArg Prod.fst hya
        · simpa using congrArg Prod.snd hxa
      have hbcoord : D.coord b = (0, 0) := by
        ext
        · simpa using congrArg Prod.fst hyb
        · simpa using congrArg Prod.snd hxb
      exact hne (D.coord_inj (hacoord.trans hbcoord.symm))

lemma bottom_top_sideAtomicEdges_disjoint
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    (sideAtomicEdges D c00 c10).Disjoint (sideAtomicEdges D c11 c01) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hb := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have ht := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨xa, hxa⟩ := coord_bottom_of_onSide (D := D) h00 h10 hb.1
      obtain ⟨x'a, hx'a⟩ := coord_top_of_onSide (D := D) h11 h01 ht.1
      have hy0 := congrArg Prod.snd hxa
      have hy1 := congrArg Prod.snd hx'a
      linarith

lemma right_left_sideAtomicEdges_disjoint
    {c10 c11 c01 c00 : D.vtx}
    (h10 : D.coord c10 = (1, 0)) (h11 : D.coord c11 = (1, 1))
    (h01 : D.coord c01 = (0, 1)) (h00 : D.coord c00 = (0, 0)) :
    (sideAtomicEdges D c10 c11).Disjoint (sideAtomicEdges D c01 c00) := by
  rw [List.disjoint_left]
  intro e he₁ he₂
  induction e using Sym2.ind with
  | h a b =>
      have hr := endpoints_onSide_of_mem_sideAtomicEdges_local D he₁
      have hl := endpoints_onSide_of_mem_sideAtomicEdges_local D he₂
      obtain ⟨ya, hya⟩ := coord_right_of_onSide (D := D) h10 h11 hr.1
      obtain ⟨y'a, hy'a⟩ := coord_left_of_onSide (D := D) h01 h00 hl.1
      have hx1 := congrArg Prod.fst hya
      have hx0 := congrArg Prod.fst hy'a
      linarith















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
open scoped Classical

lemma solution
    {c00 c10 c11 c01 : D.vtx}
    (h00 : D.coord c00 = (0, 0)) (h10 : D.coord c10 = (1, 0))
    (h11 : D.coord c11 = (1, 1)) (h01 : D.coord c01 = (0, 1)) :
    (squareBoundaryEdgeList
      (sideInteriorChain D c00 c10)
      (sideInteriorChain D c10 c11)
      (sideInteriorChain D c11 c01)
      (sideInteriorChain D c01 c00)
      c00 c10 c11 c01).Nodup := by
  classical
  have h0010 : c00 ≠ c10 :=
    square_corner_ne D h00 h10 (by norm_num)
  have h1011 : c10 ≠ c11 :=
    square_corner_ne D h10 h11 (by norm_num)
  have h1101 : c11 ≠ c01 :=
    square_corner_ne D h11 h01 (by norm_num)
  have h0100 : c01 ≠ c00 :=
    square_corner_ne D h01 h00 (by norm_num)
  let B := sideAtomicEdges D c00 c10
  let R := sideAtomicEdges D c10 c11
  let T := sideAtomicEdges D c11 c01
  let L := sideAtomicEdges D c01 c00
  have hB : B.Nodup := sideAtomicEdges_nodup_local D h0010
  have hR : R.Nodup := sideAtomicEdges_nodup_local D h1011
  have hT : T.Nodup := sideAtomicEdges_nodup_local D h1101
  have hL : L.Nodup := sideAtomicEdges_nodup_local D h0100
  have hBR : B.Disjoint R :=
    bottom_right_sideAtomicEdges_disjoint D h00 h10 h11 h0010
  have hBT : B.Disjoint T :=
    bottom_top_sideAtomicEdges_disjoint D h00 h10 h11 h01
  have hBL : B.Disjoint L :=
    (left_bottom_sideAtomicEdges_disjoint D h01 h00 h10 h0100).symm
  have hRT : R.Disjoint T :=
    right_top_sideAtomicEdges_disjoint D h10 h11 h01 h1011
  have hRL : R.Disjoint L :=
    right_left_sideAtomicEdges_disjoint D h10 h11 h01 h00
  have hTL : T.Disjoint L :=
    top_left_sideAtomicEdges_disjoint D h11 h01 h00 h1101
  have hT_L : (T ++ L).Nodup := List.Nodup.append hT hL hTL
  have hR_TL : R.Disjoint (T ++ L) := by
    rw [List.disjoint_append_right]
    exact ⟨hRT, hRL⟩
  have hR_T_L : (R ++ T ++ L).Nodup := by
    simpa [List.append_assoc] using List.Nodup.append hR hT_L hR_TL
  have hB_RTL : B.Disjoint (R ++ T ++ L) := by
    rw [List.disjoint_append_right, List.disjoint_append_right]
    exact ⟨⟨hBR, hBT⟩, hBL⟩
  have hAll : (B ++ R ++ T ++ L).Nodup := by
    simpa [List.append_assoc] using List.Nodup.append hB hR_T_L hB_RTL
  simpa [squareBoundaryEdgeList, sideAtomicEdges, B, R, T, L, List.append_assoc] using hAll
