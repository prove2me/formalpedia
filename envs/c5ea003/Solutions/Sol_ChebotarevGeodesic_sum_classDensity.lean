-- Prove2me | solution 1 for ChebotarevGeodesic.sum_classDensity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:42:23.247723+00:00
-- url     : https://prove2.me/submissions/e0048034-706e-4286-b54d-caaf09e87294

-- Sol generated from Shared/ChebotarevGeodesic.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
/-
# A Formal Framework for the Chebotarev Geodesic Theorem (non-split case)

Motivated by the paper *"Chebotarev geodesic theorem: non-split case"*, which proves the
geodesic analogue of the Chebotarev density theorem for congruence subgroups of indefinite
quaternion orders with error exponent `25/36 + ε`, and deduces from it the prime geodesic
theorem with the same exponent.

The analytic input of such papers (spectral theory of the Laplacian, Kuznetsov/Selberg trace
formulae, bounds for exponential sums) is far outside the reach of a formal library today.
What *is* formalizable — and what is the actual logical skeleton of the deduction
"Chebotarev with exponent θ ⟹ prime geodesic theorem with exponent θ" — is the calculus of
**error exponents** together with the **group-theoretic bookkeeping** of conjugacy classes and
the **linear-algebraic character/orthogonality reduction** which converts the non-split problem
into the split one.

This file develops that skeleton rigorously:

* `HasErrorExponent π M θ` : `π x = M x + O(x^{θ+ε})` for every `ε > 0`;
* the exponent calculus: monotonicity, sums, scalar multiples, finite sums, finite
  linear combinations, and perturbation by lower-order terms;
* `exponent_of_inverse_transform`: if an *invertible* linear transform (a "character table")
  of a family of counting functions satisfies the estimate, then so does every member of the
  family.  This is the abstract form of the reduction of the non-split case to the split case;
* `classDensity` for a finite group, `sum_classDensity`, and
  `prime_geodesic_of_chebotarev`: summing the Chebotarev asymptotics over all conjugacy
  classes yields the prime geodesic theorem with the same exponent;
* `tendsto_atTop_of_hasErrorExponent`: an error exponent smaller than the growth exponent of
  the main term forces the qualitative Chebotarev statement (each class is hit infinitely
  often);
* the numerical record chain `25/36 < 71/102 < 7/10 < 35/48 < 3/4` and its consequences.
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic

/-! ## The exponent calculus -/


variable {π π₁ π₂ M M₁ M₂ : ℝ → ℝ} {θ θ' : ℝ}








/-! ## Reduction of the non-split case to the split case:
an invertible linear transform of counting functions -/



/-! ## Conjugacy class densities in a finite group -/


variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]



open scoped Classical in
/-- The conjugacy classes partition the group. -/
theorem sum_classSize [Fintype (ConjClasses G)] :
    ∑ C : ConjClasses G, classSize G C = Fintype.card G := by
  classical
  have := Finset.card_eq_sum_card_fiberwise
    (f := fun g : G => ConjClasses.mk g) (s := (Finset.univ : Finset G))
    (t := (Finset.univ : Finset (ConjClasses G))) (fun g _ => Finset.mem_univ _)
  simp only [classSize]
  rw [← this, Finset.card_univ]



/-! ## From the Chebotarev geodesic theorem to the prime geodesic theorem -/


/-! ## Qualitative consequence: every class is hit infinitely often -/


/-! ## The numerical record chain -/





open ChebotarevGeodesic in
open scoped Classical in
theorem solution[Fintype (ConjClasses G)] :
    ∑ C : ConjClasses G, classDensity G C = 1 := by
  classical
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos
    positivity
  simp only [classDensity]
  rw [← Finset.sum_div]
  rw [show ∑ C : ConjClasses G, (classSize G C : ℝ)
        = ((∑ C : ConjClasses G, classSize G C : ℕ) : ℝ) by push_cast; ring]
  rw [sum_classSize G]
  field_simp
