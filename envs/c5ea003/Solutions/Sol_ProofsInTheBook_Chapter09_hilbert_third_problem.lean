-- Prove2me | solution 1 for ProofsInTheBook.Chapter09.hilbert_third_problem
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T15:41:25.415268+00:00
-- url     : https://prove2.me/submissions/13431255-4f54-486b-b295-e4fae084fdb2

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











/-- Any rational multiple of `π` vanishes in the `πℚ` quotient. -/
theorem angleClassQ_rat_mul_pi (q : ℚ) : angleClassQ ((q : ℝ) * Real.pi) = 0 := by
  refine (Submodule.Quotient.mk_eq_zero piQSubmodule).mpr ?_
  rw [show ((q : ℝ) * Real.pi) = q • Real.pi from by
    rw [Rat.smul_def]]
  exact Submodule.smul_mem _ q (Submodule.subset_span (by simp))

/-- The cube's dihedral angle `π/2` is rational over `π`, so it vanishes. -/
@[simp]
theorem angleClassQ_pi_div_two : angleClassQ (Real.pi / 2) = 0 := by
  have h : Real.pi / 2 = ((1/2 : ℚ) : ℝ) * Real.pi := by push_cast; ring
  rw [h, angleClassQ_rat_mul_pi]



















-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)













































/-- Rational-target version of `dehnInvariant_const_angle`. -/
theorem dehnInvariantQ_const_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Angle) :
    dehnInvariantQ edges length (fun _ => angle) =
      dehnEdgeQ (∑ e ∈ edges, length e) angle := by
  simp [dehnInvariantQ, dehnEdgeQ, TensorProduct.sum_tmul]

/-- Rational-target version of `dehnInvariant_const_length_angle`. -/
theorem dehnInvariantQ_const_length_angle {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : ℝ) (angle : Angle) :
    dehnInvariantQ edges (fun _ => length) (fun _ => angle) =
      dehnEdgeQ ((edges.card : ℝ) * length) angle := by
  rw [dehnInvariantQ_const_angle]
  congr 1
  simp [nsmul_eq_mul]



theorem dehnInvariantQ_eq_zero_of_angles_zero {Edge Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle]
    (edges : Finset Edge) (length : Edge → ℝ) (angle : Edge → Angle)
    (hangle : ∀ e ∈ edges, angle e = 0) :
    dehnInvariantQ edges length angle = 0 := by
  unfold dehnInvariantQ
  apply Finset.sum_eq_zero
  intro e he
  unfold dehnEdgeQ
  rw [hangle e he, TensorProduct.tmul_zero]







































/--
The final invariant obstruction in Hilbert's third problem: an object with
zero Dehn invariant cannot be scissors-congruent to one with nonzero Dehn
invariant.
-/
theorem impossible_scissors_congruence_of_dehn_ne {A : Type*} [AddCommMonoid A]
    {cube tetra : A} (hcube : cube = 0) (htetra : tetra ≠ 0) : cube ≠ tetra := by
  intro h
  exact htetra (h.symm.trans hcube)

/-! ### Concrete cube and regular tetrahedron coordinate models -/





































/--
The unit cube has zero Dehn invariant: every dihedral angle is `π / 2`, which
vanishes in `ℝ / πℚ`.
-/
theorem unitCubeDehnInvariantQ_eq_zero :
    unitCubeDehnInvariantQ = 0 := by
  rw [unitCubeDehnInvariantQ]
  apply dehnInvariantQ_eq_zero_of_angles_zero
  intro e _he
  simp [cubeEdgeDihedralAngle]



theorem euclidean3_dist_sq_eq_coordinateDistSq3 (u v : Euclidean3) :
    dist u v ^ 2 = coordinateDistSq3 u v := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [coordinateDistSq3, Fin.sum_univ_three, dist_eq_norm]

























theorem regularTetrahedronVertex_dot_of_ne {i j : Fin 4} (hij : i ≠ j) :
    dot3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) = -1 := by
  fin_cases i <;> fin_cases j <;>
    simp [dot3, regularTetrahedronVertex] at hij ⊢

theorem regularTetrahedronVertex_coordinateDistSq_of_ne {i j : Fin 4} (hij : i ≠ j) :
    coordinateDistSq3 (regularTetrahedronVertex i) (regularTetrahedronVertex j) = 8 := by
  fin_cases i <;> fin_cases j <;>
    simp [coordinateDistSq3, regularTetrahedronVertex] at hij ⊢ <;> norm_num

/-- All six edges in the coordinate tetrahedron have squared length `8`. -/
theorem regularTetrahedronVertex_dist_sq_of_ne {i j : Fin 4} (hij : i ≠ j) :
    dist (regularTetrahedronVertex i) (regularTetrahedronVertex j) ^ 2 = 8 := by
  rw [euclidean3_dist_sq_eq_coordinateDistSq3]
  exact regularTetrahedronVertex_coordinateDistSq_of_ne hij













theorem regularTetrahedronEdge_univ_card :
    (Finset.univ : Finset RegularTetrahedronEdge).card = 6 := by
  decide





theorem regularTetrahedronEdgeLength_eq_sqrt8 (e : RegularTetrahedronEdge) :
    regularTetrahedronEdgeLength e = Real.sqrt 8 := by
  rw [regularTetrahedronEdgeLength]
  rw [← sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg 8)]
  rw [regularTetrahedronVertex_dist_sq_of_ne e.2.ne, Real.sq_sqrt]
  norm_num









theorem regularTetrahedronFaceNormalCosine_of_ne {i j : Fin 4} (hij : i ≠ j) :
    regularTetrahedronFaceNormalCosine i j = -1 / 3 := by
  rw [regularTetrahedronFaceNormalCosine, regularTetrahedronVertex_dot_of_ne hij]

/--
For adjacent faces of the regular tetrahedron, the cosine of the interior
dihedral angle is the negative of the cosine between outward normals.
-/
theorem regularTetrahedron_dihedralCosine_of_ne {i j : Fin 4} (hij : i ≠ j) :
    -regularTetrahedronFaceNormalCosine i j = 1 / 3 := by
  rw [regularTetrahedronFaceNormalCosine_of_ne hij]
  norm_num





theorem regularTetrahedronDihedralAngle_of_ne {i j : Fin 4} (hij : i ≠ j) :
    regularTetrahedronDihedralAngle i j = Real.arccos (1 / 3) := by
  rw [regularTetrahedronDihedralAngle, regularTetrahedron_dihedralCosine_of_ne hij]









theorem regularTetrahedronEdgeAdjacentFaceVertex0_ne_vertex1
    (e : RegularTetrahedronEdge) :
    regularTetrahedronEdgeAdjacentFaceVertex0 e ≠
      regularTetrahedronEdgeAdjacentFaceVertex1 e := by
  intro h
  let f := regularTetrahedronEdgeAdjacentFaceEquiv e
  have hsub : f.symm 0 = f.symm 1 := Subtype.ext h
  have hfin : (0 : Fin 2) = 1 := by
    calc
      (0 : Fin 2) = f (f.symm 0) := by simp
      _ = f (f.symm 1) := by rw [hsub]
      _ = 1 := by simp
  exact (by decide : (0 : Fin 2) ≠ 1) hfin



theorem regularTetrahedronEdgeDihedralAngle_eq_arccos_one_third
    (e : RegularTetrahedronEdge) :
    regularTetrahedronEdgeDihedralAngle e = Real.arccos (1 / 3) := by
  exact regularTetrahedronDihedralAngle_of_ne
    (regularTetrahedronEdgeAdjacentFaceVertex0_ne_vertex1 e)



lemma a_zmod_3 (q : ℕ) : (a q : ZMod 3) = 1 ∨ (a q : ZMod 3) = 2 := by
  induction' q using Nat.strong_induction_on with q ih
  rcases q with _ | q
  · left; rfl
  rcases q with _ | q
  · left; rfl
  · have h1 := ih (q + 1) (by omega)
    have eq : (a (q + 2) : ZMod 3) = 2 * (a (q + 1) : ZMod 3) := by
      have h_a : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
      rw [h_a]
      push_cast
      have : (9 : ZMod 3) = 0 := rfl
      rw [this, zero_mul, sub_zero]
    rcases h1 with h | h
    · right; rw [eq, h]; rfl
    · left; rw [eq, h]; rfl

lemma a_eq_T (q : ℕ) :
    (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    match q with
    | 0 =>
      simp [a, T_zero, eval_one]
    | 1 =>
      simp [a, T_one, eval_X]
    | q + 2 =>
      have ih_q  : (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := ih q (by omega)
      have ih_q1 : (a (q+1) : ℝ) = (3 : ℝ)^(q+1) * (T ℝ ((q+1 : ℕ) : ℤ)).eval (1/3) :=
        ih (q+1) (by omega)
      have hcast : ((q + 2 : ℕ) : ℤ) = (q : ℤ) + 2 := by push_cast; rfl
      have hT :
          (T ℝ ((q + 2 : ℕ) : ℤ)).eval (1/3 : ℝ) =
            2 * (1/3) * (T ℝ ((q : ℤ) + 1)).eval (1/3) -
              (T ℝ ((q : ℕ) : ℤ)).eval (1/3) := by
        rw [hcast, T_add_two]
        simp [eval_sub, eval_mul, eval_X]
      have ha_rec : (a (q + 2) : ℝ) = 2 * (a (q + 1) : ℝ) - 9 * (a q : ℝ) := by
        have : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
        rw [this]
        push_cast
        rfl
      have hcast_norm : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
      rw [hcast_norm] at ih_q1
      rw [ha_rec, hT, ih_q, ih_q1]
      have h3 : (3 : ℝ)^(q+2) = (3 : ℝ)^q * 9 := by rw [pow_add]; norm_num
      have h31 : (3 : ℝ)^(q+1) = (3 : ℝ)^q * 3 := by rw [pow_add]; norm_num
      rw [h3, h31]
      ring

theorem arccos_one_third_irrational_over_pi (q : ℚ) :
    Real.arccos (1/3) ≠ q * Real.pi := by
  intro h
  rcases eq_or_ne q 0 with hq | hq
  · rw [hq] at h
    simp at h
    revert h
    norm_num
  have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have h_int : (q.den : ℝ) * Real.arccos (1/3) = (q.num : ℝ) * Real.pi := by
    have hq_eq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by rw [Rat.cast_def]
    rw [h, hq_eq]
    field_simp
  have h_cos_lhs :
      Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
        (T ℝ (q.den : ℤ)).eval (1/3) := by
    have hcos_arccos : Real.cos (Real.arccos (1/3)) = 1/3 := by
      rw [Real.cos_arccos] <;> norm_num
    have h_symm := (T_real_cos (Real.arccos (1/3)) (q.den : ℤ)).symm
    have h_cast : ((q.den : ℤ) : ℝ) = (q.den : ℝ) := by push_cast; rfl
    rw [h_cast] at h_symm
    rw [hcos_arccos] at h_symm
    exact h_symm
  
  have h_cos_eq : Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
                  Real.cos ((q.num : ℝ) * Real.pi) := by rw [h_int]
  
  have h_sin : Real.sin ((q.num : ℝ) * Real.pi) = 0 := by
    have : (q.num : ℝ) * Real.pi = (q.num : ℤ) * Real.pi := by rfl
    rw [this, Real.sin_int_mul_pi]
  have h_cos_sq : Real.cos ((q.num : ℝ) * Real.pi) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq ((q.num : ℝ) * Real.pi)
    rw [h_sin] at this
    linarith
  have h4 : Real.cos ((q.num : ℝ) * Real.pi) = 1 ∨ Real.cos ((q.num : ℝ) * Real.pi) = -1 := sq_eq_one_iff.mp h_cos_sq

  have h_T_eval : (T ℝ (q.den : ℤ)).eval (1/3) = 1 ∨ (T ℝ (q.den : ℤ)).eval (1/3) = -1 := by
    rcases h4 with h4 | h4
    · left; rw [← h_cos_lhs, h_cos_eq, h4]
    · right; rw [← h_cos_lhs, h_cos_eq, h4]

  have h_a_eq : (a q.den : ℝ) = (3 : ℝ)^q.den ∨ (a q.den : ℝ) = -(3 : ℝ)^q.den := by
    have eq := a_eq_T q.den
    rcases h_T_eval with ht | ht
    · left; rw [eq, ht, mul_one]
    · right; rw [eq, ht]; ring
  
  have h_a_eq_int : (a q.den : ℤ) = (3 : ℤ)^q.den ∨ (a q.den : ℤ) = -(3 : ℤ)^q.den := by
    rcases h_a_eq with ha | ha
    · left; exact_mod_cast ha
    · right; exact_mod_cast ha

  have h_den_pos : 1 ≤ q.den := q.pos
  have h_a_zmod : (a q.den : ZMod 3) = 0 := by
    have h_pow : (3 : ZMod 3)^q.den = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt h_den_pos)
      rw [hk]
      have h3 : (3 : ZMod 3) = 0 := rfl
      rw [h3]
      exact zero_pow (by omega)
    rcases h_a_eq_int with ha | ha
    · have : ((a q.den : ℤ) : ZMod 3) = (3 : ZMod 3)^q.den := by
        rw [ha]
        exact Int.cast_pow 3 q.den
      rw [this, h_pow]
    · have : ((a q.den : ℤ) : ZMod 3) = -(3 : ZMod 3)^q.den := by
        rw [ha]
        have h_pow_cast : (((3 : ℤ)^q.den : ℤ) : ZMod 3) = (3 : ZMod 3)^q.den := Int.cast_pow 3 q.den
        rw [Int.cast_neg, h_pow_cast]
      rw [this, h_pow, neg_zero]
      
  rcases a_zmod_3 q.den with h1 | h2
  · rw [h_a_zmod] at h1; revert h1; decide
  · rw [h_a_zmod] at h2; revert h2; decide


/-- `arccos(1/3)` is *not* a rational multiple of `π`, hence is nonzero in the
`πℚ` quotient — this is the tetrahedron's nontrivial Dehn-edge contribution. -/
theorem angleClassQ_arccos_one_third_ne_zero :
    angleClassQ (Real.arccos (1/3)) ≠ 0 := by
  intro h
  rw [angleClassQ, Submodule.Quotient.mk_eq_zero] at h
  rw [piQSubmodule, Submodule.mem_span_singleton] at h
  obtain ⟨q, hq⟩ := h
  rw [Rat.smul_def] at hq
  exact arccos_one_third_irrational_over_pi q hq.symm





/--
Pure tensors over a field are nonzero when both factors are nonzero.  This is
the algebraic fact needed to turn the tetrahedron's nonzero angle class into a
nonzero rational Dehn invariant.
-/
theorem tensor_tmul_ne_zero_of_ne_zero {K M N : Type*} [Field K]
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

theorem dehnEdgeQ_ne_zero_of_ne_zero {Angle : Type*}
    [AddCommGroup Angle] [Module ℚ Angle] {length : ℝ} {angle : Angle}
    (hlength : length ≠ 0) (hangle : angle ≠ 0) :
    dehnEdgeQ length angle ≠ 0 := by
  exact tensor_tmul_ne_zero_of_ne_zero hlength hangle





/--
The concrete tetrahedron Dehn sum using the edge-specific adjacent-face
dihedral angle function.
-/
theorem regularTetrahedron_dehnInvariantQ_geometric_edges_eq :
    dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e)) =
      dehnEdgeQ (6 * Real.sqrt 8) (angleClassQ (Real.arccos (1 / 3))) := by
  simpa [dehnInvariantQ, regularTetrahedronEdgeLength_eq_sqrt8,
    regularTetrahedronEdgeDihedralAngle_eq_arccos_one_third,
    regularTetrahedronEdge_univ_card] using
    (dehnInvariantQ_const_length_angle
      (edges := (Finset.univ : Finset RegularTetrahedronEdge))
      (length := Real.sqrt 8)
      (angle := angleClassQ (Real.arccos (1 / 3))))

theorem regularTetrahedron_dehnInvariantQ_geometric_edges_ne_zero :
    dehnInvariantQ (Finset.univ : Finset RegularTetrahedronEdge)
        regularTetrahedronEdgeLength
        (fun e => angleClassQ (regularTetrahedronEdgeDihedralAngle e)) ≠ 0 := by
  rw [regularTetrahedron_dehnInvariantQ_geometric_edges_eq]
  exact dehnEdgeQ_ne_zero_of_ne_zero
    (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0)
      (ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 8))))
    angleClassQ_arccos_one_third_ne_zero



/--
The concrete regular tetrahedron has nonzero Dehn invariant.  The proof uses
the computed dihedral angle `arccos (1 / 3)` and the proved irrationality of
that angle over `π`.
-/
theorem regularTetrahedronDehnInvariantQ_ne_zero :
    regularTetrahedronDehnInvariantQ ≠ 0 := by
  simpa [regularTetrahedronDehnInvariantQ] using
    regularTetrahedron_dehnInvariantQ_geometric_edges_ne_zero

/--
The computed Dehn values of the unit cube and the coordinate regular
tetrahedron differ.
-/
theorem unitCube_not_regularTetrahedron_dehnQ :
    unitCubeDehnInvariantQ ≠ regularTetrahedronDehnInvariantQ := by
  exact impossible_scissors_congruence_of_dehn_ne
    unitCubeDehnInvariantQ_eq_zero
    regularTetrahedronDehnInvariantQ_ne_zero

















end ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct
open Polynomial Chebyshev
open ProofsInTheBook.Chapter09

theorem solution :
    unitCubeDehnInvariantQ ≠ regularTetrahedronDehnInvariantQ :=
  unitCube_not_regularTetrahedron_dehnQ
