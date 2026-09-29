-- Prove2me | solution 1 for ChebotarevGeodesic.exponent_of_inverse_transform
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:50:49.828506+00:00
-- url     : https://prove2.me/submissions/74c1f729-fe18-4fa2-a8f0-7580dda14deb

-- Sol generated from Shared/ChebotarevGeodesic.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Theorems.Thm_ChebotarevGeodesic_HasErrorExponent_linear_comb
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






/-! ## From the Chebotarev geodesic theorem to the prime geodesic theorem -/


/-! ## Qualitative consequence: every class is hit infinitely often -/


/-! ## The numerical record chain -/





open ChebotarevGeodesic in
theorem solution{ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hBA : B * A = 1) (f M : ι → ℝ → ℝ) (θ : ℝ)
    (h : ∀ j, HasErrorExponent (fun x => ∑ i, A j i * f i x)
                               (fun x => ∑ i, A j i * M i x) θ) (i : ι) :
    HasErrorExponent (f i) (M i) θ := by
  have hinv : ∀ k, (∑ j, B i j * A j k) = if i = k then 1 else 0 := by
    intro k
    have := congrFun (congrFun hBA i) k
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have key : ∀ (F : ι → ℝ → ℝ) (x : ℝ), ∑ j, B i j * (∑ k, A j k * F k x) = F i x := by
    intro F x
    have hswap : ∑ j, B i j * (∑ k, A j k * F k x)
        = ∑ k, (∑ j, B i j * A j k) * F k x := by
      calc ∑ j, B i j * (∑ k, A j k * F k x)
          = ∑ j, ∑ k, B i j * (A j k * F k x) := by
            exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
        _ = ∑ k, ∑ j, B i j * (A j k * F k x) := Finset.sum_comm
        _ = ∑ k, (∑ j, B i j * A j k) * F k x := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ => by ring
    rw [hswap]
    simp [hinv]
  have hlin := HasErrorExponent.linear_comb Finset.univ (fun j => B i j)
      (fun j x => ∑ k, A j k * f k x) (fun j x => ∑ k, A j k * M k x) θ
      (fun j _ => h j)
  have e₁ : (fun x => ∑ j, B i j * (∑ k, A j k * f k x)) = f i := funext (key f)
  have e₂ : (fun x => ∑ j, B i j * (∑ k, A j k * M k x)) = M i := funext (key M)
  rw [e₁, e₂] at hlin
  exact hlin
