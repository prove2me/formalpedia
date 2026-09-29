-- Prove2me | solution 1 for ChebotarevGeodesic.exponent_of_sum_and_difference
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:59:00.822532+00:00
-- url     : https://prove2.me/submissions/87a1b541-ef81-4c74-93be-b7ec397111a8

-- Sol generated from Shared/ChebotarevGeodesic.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Theorems.Thm_ChebotarevGeodesic_HasErrorExponent_add
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



/-- The estimate is stable under scalar multiplication. -/
theorem HasErrorExponent.const_mul (c : ℝ) (h : HasErrorExponent π M θ) :
    HasErrorExponent (fun x => c * π x) (fun x => c * M x) θ := by
  intro ε hε
  obtain ⟨C, hC, X, hX, hb⟩ := h ε hε
  refine ⟨(|c| + 1) * C, by positivity, X, hX, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans hX hx
  have hxpos : (0 : ℝ) ≤ x ^ (θ + ε) := Real.rpow_nonneg (by linarith) _
  calc |c * π x - c * M x| = |c| * |π x - M x| := by
        rw [← abs_mul]; ring_nf
    _ ≤ |c| * (C * x ^ (θ + ε)) := by
        exact mul_le_mul_of_nonneg_left (hb x hx) (abs_nonneg c)
    _ ≤ (|c| + 1) * C * x ^ (θ + ε) := by nlinarith [abs_nonneg c, hC.le]

/-- The estimate is additive. -/
theorem HasErrorExponent.add (h₁ : HasErrorExponent π₁ M₁ θ)
    (h₂ : HasErrorExponent π₂ M₂ θ) :
    HasErrorExponent (fun x => π₁ x + π₂ x) (fun x => M₁ x + M₂ x) θ := by
  intro ε hε
  obtain ⟨C₁, hC₁, X₁, hX₁, hb₁⟩ := h₁ ε hε
  obtain ⟨C₂, hC₂, X₂, hX₂, hb₂⟩ := h₂ ε hε
  refine ⟨C₁ + C₂, by linarith, max X₁ X₂, le_trans hX₁ (le_max_left _ _), fun x hx => ?_⟩
  have hx1 : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : X₂ ≤ x := le_trans (le_max_right _ _) hx
  calc |π₁ x + π₂ x - (M₁ x + M₂ x)| = |(π₁ x - M₁ x) + (π₂ x - M₂ x)| := by ring_nf
    _ ≤ |π₁ x - M₁ x| + |π₂ x - M₂ x| := abs_add_le _ _
    _ ≤ C₁ * x ^ (θ + ε) + C₂ * x ^ (θ + ε) := add_le_add (hb₁ x hx1) (hb₂ x hx2)
    _ = (C₁ + C₂) * x ^ (θ + ε) := by ring





/-! ## Reduction of the non-split case to the split case:
an invertible linear transform of counting functions -/



/-! ## Conjugacy class densities in a finite group -/


variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]






/-! ## From the Chebotarev geodesic theorem to the prime geodesic theorem -/


/-! ## Qualitative consequence: every class is hit infinitely often -/


/-! ## The numerical record chain -/





open ChebotarevGeodesic in
theorem solution{f₁ f₂ M₁ M₂ : ℝ → ℝ} {θ : ℝ}
    (hs : HasErrorExponent (fun x => f₁ x + f₂ x) (fun x => M₁ x + M₂ x) θ)
    (hd : HasErrorExponent (fun x => f₁ x - f₂ x) (fun x => M₁ x - M₂ x) θ) :
    HasErrorExponent f₁ M₁ θ ∧ HasErrorExponent f₂ M₂ θ := by
  constructor
  · have := _root_.HasErrorExponent.add (_root_.HasErrorExponent.const_mul (1 / 2) hs) (_root_.HasErrorExponent.const_mul (1 / 2) hd)
    have e₁ : (fun x => 1 / 2 * (f₁ x + f₂ x) + 1 / 2 * (f₁ x - f₂ x)) = f₁ := by
      funext x; ring
    have e₂ : (fun x => 1 / 2 * (M₁ x + M₂ x) + 1 / 2 * (M₁ x - M₂ x)) = M₁ := by
      funext x; ring
    rwa [e₁, e₂] at this
  · have := _root_.HasErrorExponent.add (_root_.HasErrorExponent.const_mul (1 / 2) hs) (_root_.HasErrorExponent.const_mul (-(1 / 2)) hd)
    have e₁ : (fun x => 1 / 2 * (f₁ x + f₂ x) + -(1 / 2) * (f₁ x - f₂ x)) = f₂ := by
      funext x; ring
    have e₂ : (fun x => 1 / 2 * (M₁ x + M₂ x) + -(1 / 2) * (M₁ x - M₂ x)) = M₂ := by
      funext x; ring
    rwa [e₁, e₂] at this
