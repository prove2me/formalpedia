-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter09
-- name    : ProofsInTheBook_Chapter09
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T15:35:45.74813+00:00
-- url     : https://prove2.me/theorems/44aa4a93-22f3-450f-a287-acdcf29ad4fc
-- title:
--   Rational Dehn sums for an encoded cube and tetrahedron
-- statement:
--   Let $W=\mathbb R/(\mathbb Q\pi)$, regarded as a vector space over $\mathbb Q$, and let $[\theta]$ be the class of an angle. For a finite edge set $E$, edge lengths $\ell_e$, and angle classes $\alpha_e$, define
--   $$D(E,\ell,\alpha)=\sum_{e\in E}\ell_e\otimes_{\mathbb Q}\alpha_e\in\mathbb R\otimes_{\mathbb Q}W.$$
--   The bundle specifies encoded edge sets, lengths, and dihedral angles for the unit cube and the tetrahedron with vertices $(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)$, together with their Dehn sums. These definitions support the explicit invariant comparison; they do not assert a general geometric dissection-invariance theorem.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 10, “Hilbert’s third problem: decomposing polyhedra”, pp. 67–75 (https://doi.org/10.1007/978-3-662-57265-8_10). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter09.lean#L1114. The book citation identifies the topic; this local supporting declaration need not be a separately named theorem in the book.

import Mathlib

/-!
# Chapter 9: Hilbert's third problem

From "Proofs from THE BOOK":

**Hilbert's third problem**: A regular tetrahedron cannot be cut into finitely
many polyhedral pieces and reassembled into a cube (scissors congruence fails).

The book proves this via the **Dehn invariant**: for a polyhedron P,
  D(P) = ∑_{edges e} length(e) ⊗ θ(e) ∈ ℝ ⊗_ℤ (ℝ/πℚ)
where θ(e) is the dihedral angle at edge e. Scissors-congruent polyhedra
have equal Dehn invariants. The cube has D = 0, while the regular
tetrahedron has D ≠ 0 (since arccos(1/3) is irrational over π).

Formalization status: this file closes the algebraic obstruction layer.  It
defines finite Dehn-invariant sums, the angle quotient by rational multiples
of `π`, proves that cube-like right angles vanish in that quotient, proves
`Real.arccos (1 / 3)` is not a rational multiple of `π`, and packages the
final contradiction as `chapter09` / `hilbert_third_problem` once the cube
and tetrahedron Dehn values are supplied.

Gap to the full book theorem: Mathlib does not currently provide the required
three-dimensional scissors-congruence geometry.  A complete proof still needs
a robust Euclidean polyhedron type with faces, edges, lengths, and dihedral
angles; concrete cube and regular tetrahedron models; a geometric Dehn
invariant for those polyhedra; additivity under actual finite dissections and
rigid reassembly; and the nonzero tensor-sum computation for the regular
tetrahedron's six equal edge contributions.
-/

namespace ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct
open Polynomial Chebyshev

/-!
### Dehn invariant

The key algebraic invariant. Its construction requires:
1. The tensor product ℝ ⊗[ℤ] (ℝ / πℚ)
2. Showing D is additive under dissection
3. Computing D for specific polyhedra

This is a deep geometric result requiring substantial infrastructure
beyond current Mathlib coverage.
-/

/-!
### Current Mathlib geometry coverage

The local Mathlib checkout has the raw Euclidean tools needed for coordinate
calculations in `EuclideanSpace ℝ (Fin 3)`: finite-dimensional inner product
spaces, `Affine.Simplex`, equilateral simplex lemmas, convex hulls/convex sets,
orthogonal projection, signed distance to affine subspaces, and unoriented
angles.  It does not currently expose a bundled three-dimensional polyhedron
API with faces, edges, incidence, dihedral angles, geometric Dehn invariant, or
finite scissors dissections/reassemblies.  The coordinate lemmas below are
therefore deliberately local: they verify the regular tetrahedron model and the
`1 / 3` dihedral cosine calculation, but they are not yet connected to a
global polyhedron/dissection type.
-/



/-- Rational-vector-space target for the classical Dehn invariant. -/
abbrev DehnQTarget (Angle : Type*) [AddCommGroup Angle] [Module ℚ Angle] :=
  TensorProduct ℚ ℝ Angle











/-! ### Rational multiples of `π` quotient (Tier 2 building block)

The Dehn-invariant proof of Hilbert's third problem requires the *rational*
multiples of `π` to be quotiented out, not just integer multiples.  E.g., the
cube's dihedral angle `π/2` is *not* an integer multiple of `π` but *is* a
rational multiple, so it must vanish in the angle target.  The integer
submodule `piZSubmodule` is too coarse — we need `piQSubmodule := ℚ • π`.
-/

/-- Rational multiples of `π`. -/
noncomputable def piQSubmodule : Submodule ℚ ℝ :=
  Submodule.span ℚ ({Real.pi} : Set ℝ)

/-- Real angles modulo rational multiples of `π`. -/
abbrev AngleModPiQ : Type :=
  ℝ ⧸ piQSubmodule

/-- Concrete rational target `ℝ ⊗[ℚ] (ℝ / πℚ)`. -/
abbrev DehnPiQTarget :=
  DehnQTarget AngleModPiQ

/-- The `ℝ ⧸ πℚ` projection. -/
noncomputable def angleClassQ (x : ℝ) : AngleModPiQ :=
  Submodule.Quotient.mk x

























-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)



/-- One edge contribution in the classical rational tensor target. -/
noncomputable def dehnEdgeQ {Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (length : ℝ) (angle : Angle) : DehnQTarget Angle :=
  TensorProduct.tmul ℚ length angle





















/-- Finite edge-sum model in the rational tensor target. -/
noncomputable def dehnInvariantQ {Edge Angle : Type*} [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle) :
    DehnQTarget Angle :=
  ∑ e ∈ edges, dehnEdgeQ (length e) (angle e)



































































/-! ### Concrete cube and regular tetrahedron coordinate models -/

abbrev Euclidean3 :=
  EuclideanSpace ℝ (Fin 3)



/-- The coordinate axis perpendicular to each cube face. -/
def cubeFaceAxis : Fin 6 → Fin 3 :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩,
    ⟨2, by decide⟩, ⟨2, by decide⟩]

/--
The standard regular tetrahedron centered at the origin.  Its vertices are the
four sign vectors with an even number of negative signs.
-/
noncomputable def regularTetrahedronVertex : Fin 4 → Euclidean3 :=
  ![!₂[(1 : ℝ), 1, 1], !₂[(1 : ℝ), -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

/-- Coordinate dot product in `EuclideanSpace ℝ (Fin 3)`, written explicitly for computation. -/
def dot3 (u v : Euclidean3) : ℝ :=
  u ⟨0, by decide⟩ * v ⟨0, by decide⟩ +
  u ⟨1, by decide⟩ * v ⟨1, by decide⟩ +
  u ⟨2, by decide⟩ * v ⟨2, by decide⟩









/--
Edges of the coordinate cube, represented as intersections of two adjacent
faces.  The condition `cubeFaceAxis i ≠ cubeFaceAxis j` excludes opposite
parallel face pairs, leaving the twelve actual cube edges.
-/
abbrev CubeEdge :=
  {p : Fin 6 × Fin 6 // p.1 < p.2 ∧ cubeFaceAxis p.1 ≠ cubeFaceAxis p.2}







noncomputable def unitCubeEdgeLength (_e : CubeEdge) : ℝ :=
  1

noncomputable def cubeEdgeDihedralAngle (_e : CubeEdge) : ℝ :=
  Real.pi / 2





/-- The concrete unit-cube Dehn invariant in the rational angle target. -/
noncomputable def unitCubeDehnInvariantQ : DehnPiQTarget :=
  dehnInvariantQ (Finset.univ : Finset CubeEdge)
    unitCubeEdgeLength
    (fun e => angleClassQ (cubeEdgeDihedralAngle e))



/-- Coordinate squared distance in `EuclideanSpace ℝ (Fin 3)`, written explicitly for computation. -/
def coordinateDistSq3 (u v : Euclidean3) : ℝ :=
  (u ⟨0, by decide⟩ - v ⟨0, by decide⟩) ^ 2 +
  (u ⟨1, by decide⟩ - v ⟨1, by decide⟩) ^ 2 +
  (u ⟨2, by decide⟩ - v ⟨2, by decide⟩) ^ 2







































/-- Edges of the concrete regular tetrahedron, represented once as ordered pairs `i < j`. -/
abbrev RegularTetrahedronEdge :=
  {p : Fin 4 × Fin 4 // p.1 < p.2}

/--
For an edge `e = {u, v}`, the two adjacent faces are the faces opposite the
two vertices not equal to `u` or `v`.
-/
abbrev RegularTetrahedronEdgeAdjacentFaceVertex (e : RegularTetrahedronEdge) :=
  {i : Fin 4 // i ≠ e.1.1 ∧ i ≠ e.1.2}





theorem regularTetrahedronEdgeAdjacentFaceVertex_card (e : RegularTetrahedronEdge) :
    Fintype.card (RegularTetrahedronEdgeAdjacentFaceVertex e) = 2 := by
  fin_cases e <;> decide

noncomputable def regularTetrahedronEdgeLength (e : RegularTetrahedronEdge) : ℝ :=
  dist (regularTetrahedronVertex e.1.1) (regularTetrahedronVertex e.1.2)









/--
The face opposite vertex `i` has normal parallel to `regularTetrahedronVertex i`.
Since all these normals have squared length `3`, this quotient is the cosine
between the two face normals.
-/
noncomputable def regularTetrahedronFaceNormalCosine (i j : Fin 4) : ℝ :=
  dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) / 3







/--
The dihedral angle determined by the two outward face normals opposite
vertices `i` and `j`.
-/
noncomputable def regularTetrahedronDihedralAngle (i j : Fin 4) : ℝ :=
  Real.arccos (-regularTetrahedronFaceNormalCosine i j)





noncomputable def regularTetrahedronEdgeAdjacentFaceEquiv (e : RegularTetrahedronEdge) :
    RegularTetrahedronEdgeAdjacentFaceVertex e ≃ Fin 2 :=
  Fintype.equivFinOfCardEq (regularTetrahedronEdgeAdjacentFaceVertex_card e)

noncomputable def regularTetrahedronEdgeAdjacentFaceVertex0
    (e : RegularTetrahedronEdge) : Fin 4 :=
  ((regularTetrahedronEdgeAdjacentFaceEquiv e).symm 0).1

noncomputable def regularTetrahedronEdgeAdjacentFaceVertex1
    (e : RegularTetrahedronEdge) : Fin 4 :=
  ((regularTetrahedronEdgeAdjacentFaceEquiv e).symm 1).1



noncomputable def regularTetrahedronEdgeDihedralAngle
    (e : RegularTetrahedronEdge) : ℝ :=
  regularTetrahedronDihedralAngle
    (regularTetrahedronEdgeAdjacentFaceVertex0 e)
    (regularTetrahedronEdgeAdjacentFaceVertex1 e)



/--
The regular tetrahedron has nonzero Dehn invariant because its dihedral
angle `arccos(1/3)` is irrational over `π`. This is the book's key
number-theoretic computation.
-/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (q + 2) => 2 * a (q + 1) - 9 * a q


























/-- The concrete regular tetrahedron Dehn invariant in the rational angle target. -/
noncomputable def regularTetrahedronDehnInvariantQ : DehnPiQTarget :=
  dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
    regularTetrahedronEdgeLength
    (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e))





















end ProofsInTheBook.Chapter09


