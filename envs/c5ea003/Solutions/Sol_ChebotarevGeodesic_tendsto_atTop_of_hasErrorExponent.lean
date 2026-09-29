-- Prove2me | solution 1 for ChebotarevGeodesic.tendsto_atTop_of_hasErrorExponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:03:43.788985+00:00
-- url     : https://prove2.me/submissions/23a95a2f-4d24-42b8-9e58-90e305435555

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






/-! ## From the Chebotarev geodesic theorem to the prime geodesic theorem -/


/-! ## Qualitative consequence: every class is hit infinitely often -/


/-! ## The numerical record chain -/





open ChebotarevGeodesic in
theorem solution{π M : ℝ → ℝ} {θ β c : ℝ}
    (h : HasErrorExponent π M θ) (hc : 0 < c) (hβ : 0 < β) (hθβ : θ < β)
    (hM : ∀ᶠ x in atTop, c * x ^ β ≤ M x) :
    Tendsto π atTop atTop := by
  set ε := (β - θ) / 2 with hεdef
  have hε : 0 < ε := by simp only [hεdef]; linarith
  obtain ⟨C, hC, X, hX, hb⟩ := h ε hε
  have hexp : θ + ε < β := by simp only [hεdef]; linarith
  -- eventually `C * x^(θ+ε) ≤ (c/2) * x^β`
  have hpos : 0 < β - (θ + ε) := by linarith
  have hlim : Tendsto (fun x : ℝ => x ^ (-(β - (θ + ε)))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hpos
  have hev := hlim.eventually (gt_mem_nhds (show (0:ℝ) < c / (2 * C) by positivity))
  have hsmall : ∀ᶠ x in atTop, C * x ^ (θ + ε) ≤ (c / 2) * x ^ β := by
    filter_upwards [hev, eventually_gt_atTop (0:ℝ)] with x hxlt hx0
    have hsplit : x ^ (θ + ε) = x ^ (-(β - (θ + ε))) * x ^ β := by
      rw [← Real.rpow_add hx0]; ring_nf
    have hxβ : (0:ℝ) < x ^ β := Real.rpow_pos_of_pos hx0 β
    have hkey : C * x ^ (-(β - (θ + ε))) ≤ c / 2 := by
      calc C * x ^ (-(β - (θ + ε))) ≤ C * (c / (2 * C)) :=
            mul_le_mul_of_nonneg_left hxlt.le hC.le
        _ = c / 2 := by field_simp
    rw [hsplit]
    calc C * (x ^ (-(β - (θ + ε))) * x ^ β) = (C * x ^ (-(β - (θ + ε)))) * x ^ β := by ring
      _ ≤ (c / 2) * x ^ β := mul_le_mul_of_nonneg_right hkey hxβ.le
  have hlow : ∀ᶠ x in atTop, (c / 2) * x ^ β ≤ π x := by
    filter_upwards [hM, hsmall, eventually_ge_atTop X] with x hMx hsx hxX
    have h1 : |π x - M x| ≤ C * x ^ (θ + ε) := hb x hxX
    have h2 : M x - π x ≤ C * x ^ (θ + ε) := by
      have := abs_le.mp h1
      linarith [this.1]
    linarith
  have hgrow : Tendsto (fun x : ℝ => (c / 2) * x ^ β) atTop atTop := by
    have hb : Tendsto (fun x : ℝ => x ^ β) atTop atTop :=
      tendsto_rpow_atTop hβ
    exact hb.const_mul_atTop (by positivity)
  exact tendsto_atTop_mono' atTop hlow hgrow
