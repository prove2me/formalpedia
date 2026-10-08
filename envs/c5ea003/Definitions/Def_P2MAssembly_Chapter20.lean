-- Prove2me | Definitions.Def_P2MAssembly_Chapter20
-- name    : P2MAssembly_Chapter20
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T17:08:13.059548+00:00
-- url     : https://prove2.me/theorems/f0efc6ca-b815-43d0-88ad-1fb19cf5730f
-- title:
--   Square dissections, atomic side segments, and Monsky’s valuation coloring
-- statement:
--   A square dissection consists of a natural number n, a finite vertex type V with decidable equality, an injective map $V\to\mathbb R^2$, and n ordered triples of vertices. Each triple has nonzero determinant double area. Their closed convex hulls cover exactly $[0,1]^2$, distinct hulls have disjoint topological interiors, and every triangle has area $1/n$ (a rational quotient embedded in the reals). Area is $|\det(b-a,c-a)|/2$. Oddness is not a field of this structure. T-junctions and unused vertices are allowed.
--
--   A vertex is on a side when its coordinates lie weakly between the endpoints. All vertices strictly between the endpoints are ordered by an affine side parameter, using the x coordinate unless the side is vertical. Consecutive vertices give unordered atomic edges. Each triangle contributes the concatenation of its three lists of atomic edges; an edge's multiplicity counts all its occurrences in those lists. Incident triangles are those whose list contains the edge. A square-boundary edge has its whole segment in the topological frontier of the square. Side witnesses specify endpoints and an opposite vertex, their triangle hull, nonzero area, atomic-edge membership, and the corresponding orientation sign.
--
--   The three-color construction uses a chosen extension of the rational 2-adic valuation to the real field, with values in the ordered group associated to its valuation subring. It is not an ordinary real-valued norm. A point $(x,y)$ is red if $v(x)<1$ and $v(y)<1$, green if $1\leq v(x)$ and $v(y)\leq v(x)$, and blue otherwise. A trichromatic triple has all three colors. A red–green edge has one endpoint of each of these two colors. The bundle includes indicators, transition counts along color lists, triangle-local counts, and counts on concatenated square-boundary chains, with parity represented modulo two.
--
--   The geometric auxiliary definitions include the filled parameter simplex $\{(s,t):s,t\geq0,\ s+t\leq1\}$, the affine map $(s,t)\mapsto a+s(b-a)+t(c-a)$, its linear part and its homeomorphism for nonzero determinant, and signed open half-disks $\{x:d(x,m)<\varepsilon,\ 0<\sigma\det(b-a,x-a)\}$. Orientation signs are 1 for a positive determinant and −1 otherwise. The minimum distance from a point to the finite collection of triangle sides not containing it is also defined, with value 1 when that collection is empty.
--
--   The bundle retains proof-bearing infrastructure for extending valuations (via valuation subrings) and for affine-map and determinant identities. These support the mathematical definitions; no field assumes a trichromatic triangle, an odd boundary count, or Monsky’s conclusion.
-- source:
--   Repository definitions at immutable commit: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L23 (SquareDissection), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20DissectionEngine.lean#L46 (side subdivision and atomic incidence), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20.lean#L133 (color rule), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20.lean#L275 (area), https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20.lean#L345 (chosen valuation extension), and https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20E2Cover.lean#L20 (signed half-disks). Topic: Monsky’s theorem, “One square and an odd number of triangles.” The staged DissectionEngine differs from this public file only by the documented proof-only List.count API compatibility patch; the cited definitions are unchanged. The generated bundle is bound separately by its exact artifact hash.

import Init
import Mathlib

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

/--
Mathlib does not currently expose a one-line theorem named "extend a valuation
to an arbitrary field extension".  The needed existence statement follows from
`IsLocalRing.exists_factor_valuationRing`: apply it to the valuation subring of
the base field, then use localness to prove the new valuation subring lies
exactly over the old one.
-/
theorem exists_valuationSubring_extension
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    ∃ W : ValuationSubring L,
      ∀ x : K, algebraMap K L x ∈ W ↔ x ∈ v.valuationSubring := by
  classical
  let O : ValuationSubring K := v.valuationSubring
  let f : O →+* L := (algebraMap K L).comp O.subtype
  obtain ⟨W, hWmem, _hWlocal⟩ := IsLocalRing.exists_factor_valuationRing (K := L) f
  refine ⟨W, ?_⟩
  intro x
  constructor
  · intro hxW
    by_contra hxO
    have hx0 : x ≠ 0 := by
      intro hx0
      exact hxO (by simp [hx0])
    have hxinvO : x⁻¹ ∈ O := by
      rcases O.mem_or_inv_mem x with hx | hx
      · exact (hxO hx).elim
      · exact hx
    let a : O := ⟨x⁻¹, hxinvO⟩
    let g : O →+* W := f.codRestrict W.toSubring hWmem
    have hmax : a ∈ maximalIdeal O := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      exact (ValuationSubring.inv_mem_nonunits_iff (A := O)).2 (Or.inr hxO)
    have hgmax : g a ∈ maximalIdeal W := by
      exact map_nonunit g a hmax
    have hgunit : IsUnit (g a) := by
      refine IsUnit.of_mul_eq_one (M := W) (a := g a) ⟨algebraMap K L x, hxW⟩ ?_
      ext
      simp [g, f, a, hx0]
    exact hgmax hgunit
  · intro hxO
    simpa [f, O] using hWmem ⟨x, hxO⟩

/--
Every valuation on a field extends, up to Mathlib's valuation equivalence, to
any field extension.  The extended valuation takes values in the natural value
group attached to the chosen valuation subring of the extension field.
-/
theorem exists_valuation_extension
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    ∃ W : ValuationSubring L, v.HasExtension W.valuation := by
  classical
  obtain ⟨W, hW⟩ := exists_valuationSubring_extension (K := K) (L := L) v
  refine ⟨W, ?_⟩
  refine ⟨?_⟩
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  change v x ≤ 1 ↔ W.valuation (algebraMap K L x) ≤ 1
  rw [ValuationSubring.valuation_le_one_iff, hW, Valuation.mem_valuationSubring_iff]

/-- The 2-adic valuation on `ℚ` has a valuation-subring extension to `ℝ`. -/
theorem exists_real_twoAdic_extension :
    ∃ W : ValuationSubring ℝ, (Rat.padicValuation 2).HasExtension W.valuation :=
  exists_valuation_extension (K := ℚ) (L := ℝ) (Rat.padicValuation 2)

/-- The three colors used in Monsky's 2-adic coloring argument. -/
inductive MonskyColor where
  | red | green | blue
  deriving DecidableEq, Repr, Fintype

open MonskyColor



/--
Monsky's coloring in multiplicative valuation language.  Additive conditions
`v(x) > 0` and `v(x) ≤ v(y)` become `V(x) < 1` and `V(y) ≤ V(x)` for the
multiplicative valuation used by Mathlib's `Valuation`.
-/
def colorOfValues {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (vx vy : Γ) :
    MonskyColor :=
  if vx < 1 ∧ vy < 1 then red
  else if 1 ≤ vx ∧ vy ≤ vx then green
  else blue

























/-- The Monsky coloring of a point from any multiplicative valuation. -/
def valuationColor {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (p : K × K) : MonskyColor :=
  colorOfValues (v p.1) (v p.2)









/-- Twice the oriented area of a triangle with coordinates in a ring. -/
def doubleArea {K : Type*} [Ring K] (a b c : K × K) : K :=
  (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

/-- The ordinary Euclidean area of a real triangle, expressed through `doubleArea`. -/
noncomputable def realTriangleArea (a b c : ℝ × ℝ) : ℝ :=
  |doubleArea a b c| / 2





/-- A chosen valuation subring of `ℝ` extending the 2-adic valuation on `ℚ`. -/
noncomputable def realTwoAdicSubring : ValuationSubring ℝ :=
  Classical.choose exists_real_twoAdic_extension

/-- The corresponding chosen real-valued-field valuation for Monsky coloring. -/
noncomputable def realTwoAdicValuation : Valuation ℝ realTwoAdicSubring.ValueGroup :=
  realTwoAdicSubring.valuation









/-- The chosen Monsky 2-adic coloring on the real plane. -/
noncomputable def realTwoAdicColor (p : ℝ × ℝ) : MonskyColor :=
  valuationColor realTwoAdicValuation p























/-- A triangle is trichromatic when its three vertex colors are pairwise different. -/
def TrichromaticTriangle (a b c : MonskyColor) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ a

/-- Orientation-free red-green edge predicate used in the Sperner parity count. -/
def RedGreenEdge (a b : MonskyColor) : Prop :=
  (a = red ∧ b = green) ∨ (a = green ∧ b = red)

instance decidableRedGreenEdge (a b : MonskyColor) : Decidable (RedGreenEdge a b) := by
  unfold RedGreenEdge
  infer_instance







instance decidableTrichromaticTriangle (a b c : MonskyColor) :
    Decidable (TrichromaticTriangle a b c) := by
  unfold TrichromaticTriangle
  infer_instance



















/-- `RedGreenEdge` is symmetric in its two arguments. -/
theorem redGreenEdge_symm {a b : MonskyColor} : RedGreenEdge a b ↔ RedGreenEdge b a := by
  unfold RedGreenEdge; tauto









/-- Predicate for colors lying on the red-green side of the Monsky boundary argument. -/
def colorIsRedGreen (c : MonskyColor) : Prop := c = red ∨ c = green

/-- Predicate for colors lying on the green-blue sides of the Monsky boundary argument. -/
def colorIsGreenBlue (c : MonskyColor) : Prop := c = green ∨ c = blue

/-- Predicate for colors lying on the red-blue side of the Monsky boundary argument. -/
def colorIsRedBlue (c : MonskyColor) : Prop := c = red ∨ c = blue

/-- Encode red/green colors in `ZMod 2`; blue is unused when the red-green invariant applies. -/
def colorRGParityBit : MonskyColor → ZMod 2
  | red => 0
  | green => 1
  | blue => 0

/-- Red-green transition count along a finite color chain. -/
def listRGTransitionCount : List MonskyColor → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if RedGreenEdge a b then 1 else 0) + listRGTransitionCount (b :: rest)













































/-- Red-green predicate on an unordered edge. -/
def edgeRedGreen {α : Type*} (color : α → MonskyColor) : Sym2 α → Prop :=
  Sym2.lift ⟨fun a b => RedGreenEdge (color a) (color b),
    fun _ _ => propext redGreenEdge_symm⟩



/-- Numeric indicator for red-green unordered edges. -/
noncomputable def edgeRGIndicator {α : Type*} (color : α → MonskyColor)
    (e : Sym2 α) : ℕ := by
  classical
  exact if edgeRedGreen color e then 1 else 0





/-- The local red-green edge count of one colored triangle. -/
def triangleLocalRGCount (c : MonskyColor × MonskyColor × MonskyColor) : ℕ :=
  (if RedGreenEdge c.1 c.2.1 then 1 else 0) +
  (if RedGreenEdge c.2.1 c.2.2 then 1 else 0) +
  (if RedGreenEdge c.2.2 c.1 then 1 else 0)









/-- Red-green count on a finite set of unordered boundary edges. -/
noncomputable def boundaryEdgeRedGreenCount {α : Type*} (boundary : Finset (Sym2 α))
    (color : α → MonskyColor) : ℕ :=
  (boundary.filter fun e => edgeRGIndicator color e = 1).card





/-- Consecutive unordered edges in a finite vertex chain. -/
def consecutiveEdges {α : Type*} : List α → List (Sym2 α)
  | a :: b :: rest => s(a, b) :: consecutiveEdges (b :: rest)
  | _ => []

/-- Red-green count on a finite list of unordered edges. -/
noncomputable def listEdgeRGCount {α : Type*} (edges : List (Sym2 α))
    (color : α → MonskyColor) : ℕ :=
  (edges.filter fun e => edgeRGIndicator color e = 1).length







/--
Boundary edge list for a square-like contour, split into the four side chains
and the four corner vertices.
-/
def squareBoundaryEdgeList {α : Type*} (bottom right top left : List α)
    (bottomLeft bottomRight topRight topLeft : α) : List (Sym2 α) :=
  consecutiveEdges (bottomLeft :: bottom ++ [bottomRight]) ++
  consecutiveEdges (bottomRight :: right ++ [topRight]) ++
  consecutiveEdges (topRight :: top ++ [topLeft]) ++
  consecutiveEdges (topLeft :: left ++ [bottomLeft])

































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

/-- `doubleArea a b c` equals the determinant of the 2×2 matrix whose columns
are the edge vectors `b - a` and `c - a`. -/
theorem doubleArea_eq_det_fin_two (a b c : ℝ × ℝ) :
    doubleArea a b c =
      (!![b.1 - a.1, c.1 - a.1;
          b.2 - a.2, c.2 - a.2] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.det_fin_two_of]
  unfold doubleArea
  ring



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

/-- The affine parametrization of the triangle: `(s, t) ↦ a + s • (b - a) + t • (c - a)`. -/
def triangleAffine (a b c : ℝ × ℝ) (st : ℝ × ℝ) : ℝ × ℝ :=
  a + st.1 • (b - a) + st.2 • (c - a)









/-- The set of filled standard 2-simplex parameters: `{(s, t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}`. -/
def filled2Simplex : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}







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

/-- The linear part of `triangleAffine a b c`: `(s, t) ↦ s • (b - a) + t • (c - a)`. -/
noncomputable def triangleEdgeMap (a b c : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun st := st.1 • (b - a) + st.2 • (c - a)
  map_add' u v := by
    show (u + v).1 • (b - a) + (u + v).2 • (c - a) =
        u.1 • (b - a) + u.2 • (c - a) + (v.1 • (b - a) + v.2 • (c - a))
    ext
    · show ((u + v).1 * (b - a).1 + (u + v).2 * (c - a).1 : ℝ) =
          u.1 * (b - a).1 + u.2 * (c - a).1 + (v.1 * (b - a).1 + v.2 * (c - a).1)
      simp [Prod.add_def]; ring
    · show ((u + v).1 * (b - a).2 + (u + v).2 * (c - a).2 : ℝ) =
          u.1 * (b - a).2 + u.2 * (c - a).2 + (v.1 * (b - a).2 + v.2 * (c - a).2)
      simp [Prod.add_def]; ring
  map_smul' r v := by
    show (r • v).1 • (b - a) + (r • v).2 • (c - a) =
        r • (v.1 • (b - a) + v.2 • (c - a))
    ext
    · show ((r • v).1 * (b - a).1 + (r • v).2 * (c - a).1 : ℝ) =
          r * (v.1 * (b - a).1 + v.2 * (c - a).1)
      simp [Prod.smul_def]; ring
    · show ((r • v).1 * (b - a).2 + (r • v).2 * (c - a).2 : ℝ) =
          r * (v.1 * (b - a).2 + v.2 * (c - a).2)
      simp [Prod.smul_def]; ring

theorem triangleEdgeMap_apply (a b c st : ℝ × ℝ) :
    triangleEdgeMap a b c st = st.1 • (b - a) + st.2 • (c - a) := rfl



/-- The determinant of `triangleEdgeMap a b c` equals `doubleArea a b c`. -/
theorem det_triangleEdgeMap (a b c : ℝ × ℝ) :
    LinearMap.det (triangleEdgeMap a b c) = doubleArea a b c := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), doubleArea_eq_det_fin_two]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr]
  fin_cases j <;> fin_cases i <;>
    simp [triangleEdgeMap_apply, Module.Basis.finTwoProd_zero,
          Module.Basis.finTwoProd_one]







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

abbrev P := ℝ × ℝ















noncomputable def triangleAffineMap (a b c : P) : P →ᵃ[ℝ] P where
  toFun := triangleAffine a b c
  linear := triangleEdgeMap a b c
  map_vadd' := by
    intro p v
    ext <;> simp [triangleAffine, triangleEdgeMap_apply] <;> ring



noncomputable def triangleAffineHomeomorph (a b c : P)
    (hnd : doubleArea a b c ≠ 0) : P ≃ₜ P :=
  let e : P ≃ₗ[ℝ] P :=
    LinearMap.equivOfDetNeZero (triangleEdgeMap a b c) (by
      rwa [det_triangleEdgeMap])
  e.toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft a)





































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

abbrev P := ℝ × ℝ

/-- The open disk around `m`, cut by a strict signed half-plane for the oriented
line through `a,b`.  The sign is normally `1` or `-1`. -/
def signedOpenHalfDisk (a b m : P) (ε σ : ℝ) : Set P :=
  {x | dist x m < ε ∧ 0 < σ * doubleArea a b x}









end Chapter20E2Cover

export Chapter20E2Cover
  (signedOpenHalfDisk
   
   
   
   )

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

/-- A genuine dissection of the unit square into `n` triangles of equal area.
`vtx` ranges over *all* triangle corners, so a side may carry T-vertices in its
relative interior. -/
structure SquareDissection where
  n : ℕ
  vtx : Type
  [vtxFin : Fintype vtx]
  [vtxDec : DecidableEq vtx]
  coord : vtx → ℝ × ℝ
  coord_inj : Function.Injective coord
  tri : Fin n → vtx × vtx × vtx
  nondeg : ∀ i, doubleArea (coord (tri i).1) (coord (tri i).2.1) (coord (tri i).2.2) ≠ 0
  cover : (⋃ i, convexHull ℝ {coord (tri i).1, coord (tri i).2.1, coord (tri i).2.2})
            = Set.Icc (0, 0) (1, 1)
  disjoint_int : ∀ i j, i ≠ j →
    Disjoint (interior (convexHull ℝ
        {coord (tri i).1, coord (tri i).2.1, coord (tri i).2.2}))
      (interior (convexHull ℝ
        {coord (tri j).1, coord (tri j).2.1, coord (tri j).2.2}))
  equalArea : ∀ i, realTriangleArea (coord (tri i).1) (coord (tri i).2.1)
                     (coord (tri i).2.2) = (((1 : ℚ) / n : ℚ) : ℝ)

attribute [instance] SquareDissection.vtxFin SquareDissection.vtxDec

variable (D : SquareDissection)

/-- A vertex `w` lies on the closed side `(p,q)`. -/
def OnSide (p q w : D.vtx) : Prop :=
  Wbtw ℝ (D.coord p) (D.coord w) (D.coord q)

/-- Affine parameter of `w` along side `(p,q)` (only used to order vertices). -/
noncomputable def sideParam (p q w : D.vtx) : ℝ :=
  if (D.coord q).1 ≠ (D.coord p).1
  then ((D.coord w).1 - (D.coord p).1) / ((D.coord q).1 - (D.coord p).1)
  else ((D.coord w).2 - (D.coord p).2) / ((D.coord q).2 - (D.coord p).2)

open scoped Classical in
/-- Vertices strictly between `p` and `q` on the side, ordered by `sideParam`. -/
noncomputable def sideInteriorChain (p q : D.vtx) : List D.vtx :=
  (Finset.univ.filter (fun w => OnSide D p q w ∧ w ≠ p ∧ w ≠ q)).toList.insertionSort
    (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)

/-- Atomic edges along side `(p,q)`. -/
noncomputable def sideAtomicEdges (p q : D.vtx) : List (Sym2 D.vtx) :=
  consecutiveEdges (p :: sideInteriorChain D p q ++ [q])

/-- All atomic edges contributed by triangle `i`. -/
noncomputable def triAtomicEdges (i : Fin D.n) : List (Sym2 D.vtx) :=
  sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 ++
  sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2 ++
  sideAtomicEdges D (D.tri i).2.2 (D.tri i).1

/-- Multiplicity of an unordered edge across all triangle atomic boundaries. -/
noncomputable def atomicMult (e : Sym2 D.vtx) : ℕ :=
  ∑ i : Fin D.n, (triAtomicEdges D i).count e

/-- `e` occurs as an atomic edge of some triangle. -/
def IsAtomicEdge (e : Sym2 D.vtx) : Prop := ∃ i, e ∈ triAtomicEdges D i

/-- `e` lies on the boundary of the unit square. -/
def OnSquareBoundary (e : Sym2 D.vtx) : Prop :=
  e ∈ Sym2.fromRel (r := fun p q : D.vtx =>
    segment ℝ (D.coord p) (D.coord q) ⊆
      frontier (Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1))) (by
        intro a b h
        rwa [segment_symm])

abbrev unitSquareSet : Set (ℝ × ℝ) :=
  Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)

noncomputable def triHull (i : Fin D.n) : Set (ℝ × ℝ) :=
  convexHull ℝ {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2}

open scoped Classical in
noncomputable def incidentTris (e : Sym2 D.vtx) : Finset (Fin D.n) :=
  Finset.univ.filter fun i => e ∈ triAtomicEdges D i



































































































































noncomputable def realSign (x : ℝ) : ℝ :=
  if 0 < x then 1 else -1















noncomputable def incidentOppSign (a b : D.vtx) (i : Fin D.n) : ℝ :=
  if s(a, b) ∈ sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 then
    realSign (doubleArea (D.coord a) (D.coord b) (D.coord (D.tri i).2.2))
  else if s(a, b) ∈ sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2 then
    realSign (doubleArea (D.coord a) (D.coord b) (D.coord (D.tri i).1))
  else
    realSign (doubleArea (D.coord a) (D.coord b) (D.coord (D.tri i).2.1))







structure IncidentSideWitness (i : Fin D.n) (a b : D.vtx) where
  p : D.vtx
  q : D.vtx
  r : D.vtx
  hmem : s(a, b) ∈ sideAtomicEdges D p q
  hHull : triHull D i =
    convexHull ℝ ({D.coord p, D.coord q, D.coord r} : Set (ℝ × ℝ))
  hnd : doubleArea (D.coord p) (D.coord q) (D.coord r) ≠ 0
  hopp : incidentOppSign D a b i =
    realSign (doubleArea (D.coord a) (D.coord b) (D.coord r))





def triSideP (i : Fin D.n) (j : Fin 3) : D.vtx :=
  ![(D.tri i).1, (D.tri i).2.1, (D.tri i).2.2] j

def triSideQ (i : Fin D.n) (j : Fin 3) : D.vtx :=
  ![(D.tri i).2.1, (D.tri i).2.2, (D.tri i).1] j

def triSideR (i : Fin D.n) (j : Fin 3) : D.vtx :=
  ![(D.tri i).2.2, (D.tri i).1, (D.tri i).2.1] j

def triSideSegment (ij : Fin D.n × Fin 3) : Set (ℝ × ℝ) :=
  segment ℝ (D.coord (triSideP D ij.1 ij.2)) (D.coord (triSideQ D ij.1 ij.2))







































open scoped Classical in
noncomputable def sideSegmentsNotContaining (m : ℝ × ℝ) :
    Finset (Fin D.n × Fin 3) :=
  Finset.univ.filter fun ij => m ∉ triSideSegment D ij

open scoped Classical in
noncomputable def minDistToSidesNotContaining (m : ℝ × ℝ) : ℝ :=
  if hne : (sideSegmentsNotContaining D m).Nonempty then
    (sideSegmentsNotContaining D m).inf' hne
      (fun ij => Metric.infDist m (triSideSegment D ij))
  else 1































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

/-- Multiplicity of an unordered edge across a finite family of edge-lists. -/
def familyEdgeMult {n : ℕ} (f : Fin n → List (Sym2 V)) (e : Sym2 V) : ℕ :=
  ∑ i : Fin n, (f i).count e











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





















abbrev unitSquareSetLocal : Set (ℝ × ℝ) :=
  Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1)

noncomputable def triHullLocal (i : Fin D.n) : Set (ℝ × ℝ) :=
  convexHull ℝ {D.coord (D.tri i).1, D.coord (D.tri i).2.1, D.coord (D.tri i).2.2}























































































































































































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


