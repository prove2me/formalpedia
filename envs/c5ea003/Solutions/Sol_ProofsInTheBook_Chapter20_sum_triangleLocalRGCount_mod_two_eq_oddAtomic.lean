-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.sum_triangleLocalRGCount_mod_two_eq_oddAtomic
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:51:14.717654+00:00
-- url     : https://prove2.me/submissions/44b13c9e-26a4-43f1-940d-66bc536e8daa

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





















theorem colorOfValues_eq_red_iff {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} :
    colorOfValues vx vy = red ↔ vx < 1 ∧ vy < 1 := by
  unfold colorOfValues
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred]
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · simp [hred, hgreen]
    · simp [hred, hgreen]

theorem colorOfValues_green_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} (h : colorOfValues vx vy = green) : 1 ≤ vx ∧ vy ≤ vx := by
  unfold colorOfValues at h
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred] at h
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · exact hgreen
    · simp [hred, hgreen] at h



theorem colorOfValues_blue_lt_and_one_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} (h : colorOfValues vx vy = blue) : vx < vy ∧ 1 ≤ vy := by
  unfold colorOfValues at h
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred] at h
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · simp [hred, hgreen] at h
    · simp [hred, hgreen] at h
      have hvx_lt_one_or : vx < 1 ∨ 1 ≤ vx := lt_or_ge vx 1
      have hvy_lt_or : vy < 1 ∨ 1 ≤ vy := lt_or_ge vy 1
      constructor
      · by_contra hnot
        have hvyle : vy ≤ vx := le_of_not_gt hnot
        rcases hvx_lt_one_or with hvxlt | hvxge
        · have hvylt : vy < 1 := lt_of_le_of_lt hvyle hvxlt
          exact hred ⟨hvxlt, hvylt⟩
        · exact hgreen ⟨hvxge, hvyle⟩
      · rcases hvy_lt_or with hvylt | hvyge
        · rcases hvx_lt_one_or with hvxlt | hvxge
          · exact (hred ⟨hvxlt, hvylt⟩).elim
          · exact (hgreen ⟨hvxge, (le_of_lt hvylt).trans hvxge⟩).elim
        · exact hvyge

















/--
A red-green-blue triangle has double area with valuation at least `1` in
Mathlib's multiplicative convention.  This is the valuation side of Monsky's
area contradiction; an odd equal subdivision will later give double area
`2 / n`, whose 2-adic valuation is `< 1`.
-/
theorem valuation_doubleArea_red_green_blue
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {r g b : K × K}
    (hr : valuationColor v r = red)
    (hg : valuationColor v g = green)
    (hb : valuationColor v b = blue) :
    1 ≤ v (doubleArea r g b) := by
  have hr_lt : v r.1 < 1 ∧ v r.2 < 1 := colorOfValues_eq_red_iff.mp hr
  have hg_le : 1 ≤ v g.1 ∧ v g.2 ≤ v g.1 := colorOfValues_green_le hg
  have hb_lt : v b.1 < v b.2 ∧ 1 ≤ v b.2 := colorOfValues_blue_lt_and_one_le hb
  have hrgx : v (g.1 - r.1) = v g.1 := by
    exact v.map_sub_eq_of_lt_left (lt_of_lt_of_le hr_lt.1 hg_le.1)
  have hrby : v (b.2 - r.2) = v b.2 := by
    exact v.map_sub_eq_of_lt_left (lt_of_lt_of_le hr_lt.2 hb_lt.2)
  have hrgy_le : v (g.2 - r.2) ≤ v g.1 := by
    exact v.map_sub_le hg_le.2 ((le_of_lt hr_lt.2).trans hg_le.1)
  have hrbx_lt : v (b.1 - r.1) < v b.2 := by
    exact lt_of_le_of_lt (v.map_sub b.1 r.1)
      (max_lt hb_lt.1 (lt_of_lt_of_le hr_lt.1 hb_lt.2))
  let t₁ : K := (g.1 - r.1) * (b.2 - r.2)
  let t₂ : K := (b.1 - r.1) * (g.2 - r.2)
  have ht₁ : v t₁ = v g.1 * v b.2 := by
    simp [t₁, hrgx, hrby]
  have ht₂_lt : v t₂ < v g.1 * v b.2 := by
    have hle :
        v (b.1 - r.1) * v (g.2 - r.2) ≤ v (b.1 - r.1) * v g.1 :=
      mul_le_mul' le_rfl hrgy_le
    have hlt : v (b.1 - r.1) * v g.1 < v b.2 * v g.1 := by
      exact (strictMono_mul_right_of_pos (lt_of_lt_of_le zero_lt_one hg_le.1)) hrbx_lt
    have hmul : v (b.1 - r.1) * v (g.2 - r.2) < v b.2 * v g.1 :=
      lt_of_le_of_lt hle hlt
    simpa [t₂, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdet : v (doubleArea r g b) = v g.1 * v b.2 := by
    change v (t₁ - t₂) = v g.1 * v b.2
    rw [v.map_sub_eq_of_lt_left]
    · exact ht₁
    · rw [ht₁]
      exact ht₂_lt
  rw [hdet]
  calc
    (1 : Γ) = 1 * 1 := by rw [mul_one]
    _ ≤ v g.1 * v b.2 := mul_le_mul' hg_le.1 hb_lt.2



















































theorem trichromatic_of_eq_red_green_blue {a b c : MonskyColor}
    (ha : a = red) (hb : b = green) (hc : c = blue) : TrichromaticTriangle a b c := by
  subst a
  subst b
  subst c
  simp [TrichromaticTriangle]





































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

theorem edgeRGIndicator_eq_zero_or_one {α : Type*} (color : α → MonskyColor)
    (e : Sym2 α) :
    edgeRGIndicator color e = 0 ∨ edgeRGIndicator color e = 1 := by
  classical
  unfold edgeRGIndicator
  by_cases h : edgeRedGreen color e <;> simp [h]





















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





























open scoped Classical in
lemma mem_sideInteriorChain_iff {p q w : D.vtx} :
    w ∈ sideInteriorChain D p q ↔ OnSide D p q w ∧ w ≠ p ∧ w ≠ q := by
  classical
  unfold sideInteriorChain
  rw [List.mem_insertionSort, Finset.mem_toList]
  simp [OnSide]









lemma onSide_left (p q : D.vtx) : OnSide D p q p := by
  exact wbtw_self_left (R := ℝ) (D.coord p) (D.coord q)

lemma onSide_right (p q : D.vtx) : OnSide D p q q := by
  exact wbtw_self_right (R := ℝ) (D.coord p) (D.coord q)

lemma sideInteriorChain_onSide {p q w : D.vtx}
    (hw : w ∈ sideInteriorChain D p q) : OnSide D p q w :=
  (mem_sideInteriorChain_iff (D := D)).mp hw |>.1





























lemma onSide_of_mem_sideChain {p q w : D.vtx}
    (hw : w ∈ p :: sideInteriorChain D p q ++ [q]) : OnSide D p q w := by
  rw [List.mem_append] at hw
  rcases hw with hw | hw
  · rw [List.mem_cons] at hw
    rcases hw with hwp | hw
    · rw [hwp]
      exact onSide_left D p q
    · exact sideInteriorChain_onSide D hw
  · rw [List.mem_singleton] at hw
    rw [hw]
    exact onSide_right D p q





























































































































































































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

/-- **Lemma 1, valuation form, any rainbow ordering.** For a trichromatic triple
in the plane (one red, one green, one blue vertex, in any order), the 2-adic
valuation of the signed double area is at least `1`.  The red–green–blue case is
`valuation_doubleArea_red_green_blue`; the other five vertex orderings reduce to
it because `doubleArea` only changes sign under a transposition and the valuation
is sign-blind (`v (-t) = v t`). -/
theorem one_le_realTwoAdicValuation_doubleArea_of_trichromatic {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c)) :
    1 ≤ realTwoAdicValuation (doubleArea a b c) := by
  have base : ∀ x y z : ℝ × ℝ,
      realTwoAdicColor x = red → realTwoAdicColor y = green →
      realTwoAdicColor z = blue →
      1 ≤ realTwoAdicValuation (doubleArea x y z) := by
    intro x y z hx hy hz
    exact valuation_doubleArea_red_green_blue realTwoAdicValuation hx hy hz
  have vneg : ∀ t : ℝ, realTwoAdicValuation (-t) = realTwoAdicValuation t :=
    fun t => realTwoAdicValuation.map_neg t
  rcases htri with ⟨hab, hbc, hca⟩
  rcases hA : realTwoAdicColor a with _ | _ | _ <;>
    rcases hB : realTwoAdicColor b with _ | _ | _ <;>
      rcases hC : realTwoAdicColor c with _ | _ | _ <;>
        (try rw [hA] at hab hca) <;> (try rw [hB] at hab hbc) <;>
        (try rw [hC] at hbc hca) <;>
        first
          | exact absurd rfl hab
          | exact absurd rfl hbc
          | exact absurd rfl hca
          | exact base a b c hA hB hC
          | (rw [show doubleArea a b c = -(doubleArea a c b) by
                unfold doubleArea; ring, vneg]
             exact base a c b hA hC hB)
          | (rw [show doubleArea a b c = -(doubleArea b a c) by
                unfold doubleArea; ring, vneg]
             exact base b a c hB hA hC)
          | (rw [show doubleArea a b c = doubleArea b c a by
                unfold doubleArea; ring]
             exact base b c a hB hC hA)
          | (rw [show doubleArea a b c = doubleArea c a b by
                unfold doubleArea; ring]
             exact base c a b hC hA hB)
          | (rw [show doubleArea a b c = -(doubleArea c b a) by
                unfold doubleArea; ring, vneg]
             exact base c b a hC hB hA)

/-- **Corollary to Lemma 1 (≤ 2 colors per line).** Three collinear points of the
plane cannot form a rainbow triangle.  Their signed double area is `0`, but a
rainbow triple has `realTwoAdicValuation (doubleArea …) ≥ 1 > 0 = v 0`.  This is
the fact that on any straight line at most two of the three Monsky colors occur,
which drives the per-side parity bookkeeping (E3). -/
theorem not_trichromatic_of_collinear {a b c : ℝ × ℝ}
    (hcol : doubleArea a b c = 0) :
    ¬ TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
        (realTwoAdicColor c) := by
  intro htri
  have h1 := one_le_realTwoAdicValuation_doubleArea_of_trichromatic htri
  rw [hcol, map_zero] at h1
  exact one_ne_zero (le_antisymm h1 zero_le_one)

/-! ### E3 — per-side red–green parity (general, from ≤2 colors per line)

Along one straight side of a triangle the dissection vertices form a chain
`a :: middle ++ [b]` lying on a single line, so by the ≤2-colors corollary the
chain uses at most two of the three colors.  In that situation the number of
red–green atomic segments along the chain has exactly the parity of "the two
endpoints `a, b` form a red–green pair".  This upgrades the proved
`listRGTransitionCount_*` side lemmas (which fix the colors per side) to an
arbitrary side of an arbitrary triangle. -/

theorem odd_listRGTransitionCount_iff_endpoints
    (a b : MonskyColor) (middle : List MonskyColor)
    (h2 : ∃ x y : MonskyColor, ∀ c ∈ a :: middle ++ [b], c = x ∨ c = y) :
    Odd (listRGTransitionCount (a :: middle ++ [b])) ↔ RedGreenEdge a b := by
  have hamem : a ∈ a :: middle ++ [b] := by simp
  have hbmem : b ∈ a :: middle ++ [b] := by simp
  by_cases hr : red ∈ a :: middle ++ [b]
  · by_cases hg : green ∈ a :: middle ++ [b]
    · -- both red and green occur; a third colour blue would give three colours
      -- in a chain that uses at most two, so blue is absent and the chain is
      -- entirely red/green.
      have hblue : blue ∉ a :: middle ++ [b] := by
        intro hbl
        obtain ⟨x, y, hxy⟩ := h2
        have hsub : ({red, green, blue} : Finset MonskyColor) ⊆ {x, y} := by
          intro c hc
          have hcxy : c = x ∨ c = y := by
            fin_cases hc
            · exact hxy red hr
            · exact hxy green hg
            · exact hxy blue hbl
          rcases hcxy with rfl | rfl <;> simp
        have hcard := Finset.card_le_card hsub
        have h3 : ({red, green, blue} : Finset MonskyColor).card = 3 := by decide
        have h2card : ({x, y} : Finset MonskyColor).card ≤ 2 := by
          apply le_trans (Finset.card_insert_le _ _); simp
        omega
      have hall : ∀ c ∈ a :: middle ++ [b], colorIsRedGreen c := by
        intro c hc
        cases c with
        | red => exact Or.inl rfl
        | green => exact Or.inr rfl
        | blue => exact absurd hc hblue
      have hz := listRGTransitionCount_cons_append_zmod (a := a) (b := b) middle hall
      rw [← ZMod.natCast_eq_one_iff_odd, hz]
      have ha : colorIsRedGreen a := hall a hamem
      have hb : colorIsRedGreen b := hall b hbmem
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
    · -- green absent ⇒ chain is red/blue ⇒ no red–green segments
      have hall : ∀ c ∈ a :: middle ++ [b], colorIsRedBlue c := by
        intro c hc
        cases c with
        | red => exact Or.inl rfl
        | green => exact absurd hc hg
        | blue => exact Or.inr rfl
      have hzero := listRGTransitionCount_eq_zero_of_redBlue _ hall
      rw [hzero]
      have ha : colorIsRedBlue a := hall a hamem
      have hb : colorIsRedBlue b := hall b hbmem
      constructor
      · intro h; exact absurd h (by decide)
      · intro h; exact absurd h (not_redGreenEdge_of_redBlue ha hb)
  · -- red absent ⇒ chain is green/blue ⇒ no red–green segments
    have hall : ∀ c ∈ a :: middle ++ [b], colorIsGreenBlue c := by
      intro c hc
      cases c with
      | red => exact absurd hc hr
      | green => exact Or.inl rfl
      | blue => exact Or.inr rfl
    have hzero := listRGTransitionCount_eq_zero_of_greenBlue _ hall
    rw [hzero]
    have ha : colorIsGreenBlue a := hall a hamem
    have hb : colorIsGreenBlue b := hall b hbmem
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (not_redGreenEdge_of_greenBlue ha hb)

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

/-- A list of points in which every triple is collinear (`doubleArea = 0`) omits
at least one Monsky colour: otherwise red, green, blue witnesses would form a
collinear rainbow triple, impossible by `not_trichromatic_of_collinear`. -/
theorem exists_missing_color_of_collinear_list (pts : List (ℝ × ℝ))
    (hcol : ∀ a ∈ pts, ∀ b ∈ pts, ∀ c ∈ pts, doubleArea a b c = 0) :
    ∃ col : MonskyColor, ∀ p ∈ pts, realTwoAdicColor p ≠ col := by
  by_contra h
  push_neg at h
  obtain ⟨pr, hpr, hcr⟩ := h red
  obtain ⟨pg, hpg, hcg⟩ := h green
  obtain ⟨pb, hpb, hcb⟩ := h blue
  have hc0 : doubleArea pr pg pb = 0 := hcol pr hpr pg hpg pb hpb
  exact not_trichromatic_of_collinear hc0
    (by rw [hcr, hcg, hcb]; exact trichromatic_of_eq_red_green_blue rfl rfl rfl)

/-- A collinear list of points uses at most two colours. -/
theorem exists_two_colors_of_collinear_list (pts : List (ℝ × ℝ))
    (hcol : ∀ a ∈ pts, ∀ b ∈ pts, ∀ c ∈ pts, doubleArea a b c = 0) :
    ∃ x y : MonskyColor, ∀ p ∈ pts, realTwoAdicColor p = x ∨ realTwoAdicColor p = y := by
  obtain ⟨col, hmiss⟩ := exists_missing_color_of_collinear_list pts hcol
  cases col with
  | red =>
      refine ⟨green, blue, fun p hp => ?_⟩
      have hne := hmiss p hp
      cases h : realTwoAdicColor p with
      | red => exact absurd h hne
      | green => exact Or.inl rfl
      | blue => exact Or.inr rfl
  | green =>
      refine ⟨red, blue, fun p hp => ?_⟩
      have hne := hmiss p hp
      cases h : realTwoAdicColor p with
      | red => exact Or.inl rfl
      | green => exact absurd h hne
      | blue => exact Or.inr rfl
  | blue =>
      refine ⟨red, green, fun p hp => ?_⟩
      have hne := hmiss p hp
      cases h : realTwoAdicColor p with
      | red => exact Or.inl rfl
      | green => exact Or.inr rfl
      | blue => exact absurd h hne

/-- **E3 on a subdivided side, point form.** For a side whose intermediate
vertices give the colour chain `ca :: middle ++ [cb]` and whose underlying points
are pairwise-triple-collinear, the number of red–green atomic segments has the
parity of "the two endpoint colours form a red–green pair". -/
theorem odd_sideRG_iff_endpoints_of_collinear
    (endpts mids : List (ℝ × ℝ)) (a b : ℝ × ℝ)
    (hchain : endpts = a :: mids ++ [b])
    (hcol : ∀ x ∈ endpts, ∀ y ∈ endpts, ∀ z ∈ endpts, doubleArea x y z = 0) :
    Odd (listRGTransitionCount
        (realTwoAdicColor a :: mids.map realTwoAdicColor ++ [realTwoAdicColor b])) ↔
      RedGreenEdge (realTwoAdicColor a) (realTwoAdicColor b) := by
  obtain ⟨x, y, hxy⟩ := exists_two_colors_of_collinear_list endpts hcol
  apply odd_listRGTransitionCount_iff_endpoints
  refine ⟨x, y, ?_⟩
  intro c hc
  -- the colour chain is `endpts.map realTwoAdicColor`, so `c` is some point's colour
  have hc' : c ∈ endpts.map realTwoAdicColor := by
    rw [hchain]; simpa using hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
  exact hxy p hp

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



/-- The red–green count of one edge-list equals the indicator-weighted sum of
edge multiplicities over the (finite) edge type. -/
theorem listEdgeRGCount_eq_sum_count (l : List (Sym2 V)) (color : V → MonskyColor) :
    listEdgeRGCount l color = ∑ e : Sym2 V, l.count e * edgeRGIndicator color e := by
  classical
  unfold listEdgeRGCount
  induction l with
  | nil => simp
  | cons a t ih =>
      have key : (∑ e : Sym2 V, (a :: t).count e * edgeRGIndicator color e)
          = (∑ e : Sym2 V, t.count e * edgeRGIndicator color e) + edgeRGIndicator color a := by
        have hpt : ∀ e : Sym2 V, (a :: t).count e * edgeRGIndicator color e
            = t.count e * edgeRGIndicator color e
              + (if a = e then edgeRGIndicator color e else 0) := by
          intro e
          rw [List.count_cons]
          rcases eq_or_ne a e with h | h
          · subst h; simp [add_mul]
          · simp [h, Ne.symm h]
        rw [Finset.sum_congr rfl (fun e _ => hpt e), Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_ite_eq Finset.univ a (fun e => edgeRGIndicator color e)]
        simp
      rw [List.filter_cons, key]
      rcases edgeRGIndicator_eq_zero_or_one color a with h0 | h1
      · simp [h0, ih]
      · simp [h1, ih, List.length_cons]

/-- Summed over the family, the red–green count is the indicator-weighted sum of
family multiplicities. -/
theorem sum_listEdgeRGCount_eq_sum_familyMult {n : ℕ}
    (f : Fin n → List (Sym2 V)) (color : V → MonskyColor) :
    (∑ i : Fin n, listEdgeRGCount (f i) color) =
      ∑ e : Sym2 V, familyEdgeMult f e * edgeRGIndicator color e := by
  classical
  simp_rw [listEdgeRGCount_eq_sum_count]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [familyEdgeMult, Finset.sum_mul]

/-- Per-edge mod-2 reduction (mirrors `edgeMultiplicity_mul_indicator_mod_two`). -/
theorem familyEdgeMult_mul_indicator_mod_two {n : ℕ}
    (f : Fin n → List (Sym2 V)) (color : V → MonskyColor) (e : Sym2 V) :
    (familyEdgeMult f e * edgeRGIndicator color e) % 2 =
      if edgeRGIndicator color e = 1 ∧ Odd (familyEdgeMult f e) then 1 else 0 := by
  rcases edgeRGIndicator_eq_zero_or_one color e with hzero | hone
  · simp [hzero]
  · by_cases hodd : Odd (familyEdgeMult f e)
    · simp [hone, hodd, Nat.odd_iff.mp hodd]
    · have heven : Even (familyEdgeMult f e) := Nat.not_odd_iff_even.mp hodd
      simp [hone, hodd, Nat.even_iff.mp heven]

private theorem sum_nat_mod_two_eq_sum_mod_two' {α : Type*} (s : Finset α) (g : α → ℕ) :
    (∑ x ∈ s, g x) % 2 = (∑ x ∈ s, g x % 2) % 2 := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      conv_lhs => rw [Nat.add_mod (g a) _ 2, ih]
      conv_rhs => rw [Nat.add_mod (g a % 2) _ 2]
      simp

/-- **Atomic double-count.** Summed red–green counts over the family agree, mod 2,
with the number of red–green edges of odd family-multiplicity. -/
theorem sum_listEdgeRGCount_mod_two {n : ℕ}
    (f : Fin n → List (Sym2 V)) (color : V → MonskyColor) :
    (∑ i : Fin n, listEdgeRGCount (f i) color) % 2 =
      (Finset.univ.filter fun e : Sym2 V =>
        edgeRGIndicator color e = 1 ∧ Odd (familyEdgeMult f e)).card % 2 := by
  classical
  rw [sum_listEdgeRGCount_eq_sum_familyMult]
  calc
    (∑ e : Sym2 V, familyEdgeMult f e * edgeRGIndicator color e) % 2
        = (∑ e : Sym2 V, (familyEdgeMult f e * edgeRGIndicator color e) % 2) % 2 := by
          exact sum_nat_mod_two_eq_sum_mod_two' _ _
    _ = (∑ e : Sym2 V,
          if edgeRGIndicator color e = 1 ∧ Odd (familyEdgeMult f e) then 1 else 0) % 2 := by
          congr 1
          exact Finset.sum_congr rfl fun e _ =>
            familyEdgeMult_mul_indicator_mod_two f color e
    _ = (Finset.univ.filter fun e : Sym2 V =>
          edgeRGIndicator color e = 1 ∧ Odd (familyEdgeMult f e)).card % 2 := by
          rw [Finset.card_filter]

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

/-- Three points weakly between `P` and `Q` (i.e. on the segment `[P,Q]`) have
vanishing signed double area: they are collinear. -/
theorem doubleArea_eq_zero_of_wbtw {P Q a b c : ℝ × ℝ}
    (ha : Wbtw ℝ P a Q) (hb : Wbtw ℝ P b Q) (hc : Wbtw ℝ P c Q) :
    doubleArea a b c = 0 := by
  obtain ⟨ta, _, rfl⟩ := ha
  obtain ⟨tb, _, rfl⟩ := hb
  obtain ⟨tc, _, rfl⟩ := hc
  simp only [AffineMap.lineMap_apply, doubleArea, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_vsub, Prod.snd_vsub, vsub_eq_sub, vadd_eq_add]
  ring

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

/-- **Per-side E3 bridge.** The number of red-green atomic segments along side
`(p,q)` is odd iff the two endpoint colours form a red-green pair. -/
theorem odd_side_listEdgeRGCount_iff (p q : D.vtx) :
    Odd (listEdgeRGCount (sideAtomicEdges D p q) (realTwoAdicColor ∘ D.coord)) ↔
      RedGreenEdge (realTwoAdicColor (D.coord p)) (realTwoAdicColor (D.coord q)) := by
  rw [sideAtomicEdges, consecutiveEdges_RGCount_eq_listRGTransitionCount_map,
    show (p :: sideInteriorChain D p q ++ [q]).map (realTwoAdicColor ∘ D.coord)
        = realTwoAdicColor (D.coord p)
          :: ((sideInteriorChain D p q).map D.coord).map realTwoAdicColor
          ++ [realTwoAdicColor (D.coord q)] by
      simp [List.map_append, List.map_cons, List.map_map, Function.comp]]
  refine odd_sideRG_iff_endpoints_of_collinear
    ((p :: sideInteriorChain D p q ++ [q]).map D.coord)
    ((sideInteriorChain D p q).map D.coord) (D.coord p) (D.coord q)
    (by simp [List.map_append, List.map_cons]) ?_
  intro x hx y hy z hz
  obtain ⟨wx, hwx, rfl⟩ := List.mem_map.mp hx
  obtain ⟨wy, hwy, rfl⟩ := List.mem_map.mp hy
  obtain ⟨wz, hwz, rfl⟩ := List.mem_map.mp hz
  exact doubleArea_eq_zero_of_wbtw (onSide_of_mem_sideChain D hwx)
    (onSide_of_mem_sideChain D hwy) (onSide_of_mem_sideChain D hwz)

/-- Mod 2, a side's red-green atomic count equals its endpoint red-green indicator. -/
theorem side_listEdgeRGCount_mod_two (p q : D.vtx) :
    listEdgeRGCount (sideAtomicEdges D p q) (realTwoAdicColor ∘ D.coord) % 2 =
      (if RedGreenEdge (realTwoAdicColor (D.coord p)) (realTwoAdicColor (D.coord q))
        then 1 else 0) := by
  by_cases h : RedGreenEdge (realTwoAdicColor (D.coord p)) (realTwoAdicColor (D.coord q))
  · simp only [h, if_true]
    exact Nat.odd_iff.mp ((odd_side_listEdgeRGCount_iff D p q).mpr h)
  · simp only [h, if_false]
    rcases Nat.even_or_odd (listEdgeRGCount (sideAtomicEdges D p q)
      (realTwoAdicColor ∘ D.coord)) with he | ho
    · exact Nat.even_iff.mp he
    · exact absurd ((odd_side_listEdgeRGCount_iff D p q).mp ho) h

/-- **Per-triangle bridge.** The red-green atomic boundary count of triangle `i`
agrees mod 2 with its corner-colour `triangleLocalRGCount`. -/
theorem triangle_listEdgeRGCount_mod_two (i : Fin D.n) :
    listEdgeRGCount (triAtomicEdges D i) (realTwoAdicColor ∘ D.coord) % 2 =
      triangleLocalRGCount (realTwoAdicColor (D.coord (D.tri i).1),
        realTwoAdicColor (D.coord (D.tri i).2.1),
        realTwoAdicColor (D.coord (D.tri i).2.2)) % 2 := by
  rw [triAtomicEdges, listEdgeRGCount_append, listEdgeRGCount_append]
  have h1 := side_listEdgeRGCount_mod_two D (D.tri i).1 (D.tri i).2.1
  have h2 := side_listEdgeRGCount_mod_two D (D.tri i).2.1 (D.tri i).2.2
  have h3 := side_listEdgeRGCount_mod_two D (D.tri i).2.2 (D.tri i).1
  simp only [triangleLocalRGCount]
  omega







end ProofsInTheBook.Chapter20

end


set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

theorem solution :
    (∑ i : Fin D.n, triangleLocalRGCount
        (realTwoAdicColor (D.coord (D.tri i).1),
         realTwoAdicColor (D.coord (D.tri i).2.1),
         realTwoAdicColor (D.coord (D.tri i).2.2))) % 2 =
      (Finset.univ.filter fun e : Sym2 D.vtx =>
        edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
          Odd (atomicMult D e)).card % 2 := by
  classical
  -- step 1: sum of per-triangle parities (bridge), backwards
  have hstep1 : (∑ i : Fin D.n, triangleLocalRGCount
        (realTwoAdicColor (D.coord (D.tri i).1),
         realTwoAdicColor (D.coord (D.tri i).2.1),
         realTwoAdicColor (D.coord (D.tri i).2.2))) % 2 =
      (∑ i : Fin D.n, listEdgeRGCount (triAtomicEdges D i)
        (realTwoAdicColor ∘ D.coord)) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod
      (f := fun i => listEdgeRGCount (triAtomicEdges D i) (realTwoAdicColor ∘ D.coord))]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (triangle_listEdgeRGCount_mod_two D i).symm
  rw [hstep1, sum_listEdgeRGCount_mod_two (triAtomicEdges D) (realTwoAdicColor ∘ D.coord)]
  -- familyEdgeMult (triAtomicEdges D) = atomicMult D, definitionally
  rfl
