-- Prove2me | solution 1 for ProofsInTheBook.Chapter09.tensor_tmul_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T15:41:27.0142+00:00
-- url     : https://prove2.me/submissions/e826809c-e91f-4d78-acf4-412663073c7b

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter09


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















/-! ### Rational multiples of `π` quotient (Tier 2 building block)

The Dehn-invariant proof of Hilbert's third problem requires the *rational*
multiples of `π` to be quotiented out, not just integer multiples.  E.g., the
cube's dihedral angle `π/2` is *not* an integer multiple of `π` but *is* a
rational multiple, so it must vanish in the angle target.  The integer
submodule `piZSubmodule` is too coarse — we need `piQSubmodule := ℚ • π`.
-/

































-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)





























































































/-! ### Concrete cube and regular tetrahedron coordinate models -/














































































































































































end ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct
open Polynomial Chebyshev
open ProofsInTheBook.Chapter09

theorem solution {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {m : M} {n : N} (hm : m ≠ 0) (hn : n ≠ 0) :
    (m ⊗ₜ[K] n : TensorProduct K M N) ≠ 0 := by
  classical
  let s : Set N := {n}
  have hs : LinearIndepOn K id s := by
    rw [linearIndepOn_singleton_iff]
    exact hn
  let b : Module.Basis (hs.extend (Set.subset_univ s)) K N := Module.Basis.extend hs
  have hn_mem : n ∈ hs.extend (Set.subset_univ s) :=
    hs.subset_extend (Set.subset_univ s) (by simp [s])
  let i : hs.extend (Set.subset_univ s) := ⟨n, hn_mem⟩
  have hb_i : b i = n := by
    change (Module.Basis.extend hs) i = (i : N)
    exact Module.Basis.extend_apply_self hs i
  intro hzero
  have hcoeff : (TensorProduct.equivFinsuppOfBasisRight b) (m ⊗ₜ[K] n) i = 0 := by
    rw [hzero]
    simp
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply] at hcoeff
  have hrepr : b.repr n i = 1 := by
    rw [← hb_i, Module.Basis.repr_self]
    simp
  rw [hrepr, one_smul] at hcoeff
  exact hm hcoeff
