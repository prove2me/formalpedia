-- Prove2me | solution 1 for BerggrenFiniteSpectral.berggren_averaging_sum_preserved
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:09:27.909405+00:00
-- url     : https://prove2.me/submissions/55080279-52bf-4923-9d61-5088ac6f86bf

-- Sol generated from Bridges/BerggrenFiniteSpectral.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenFiniteSpectral
import Theorems.Thm_BerggrenFiniteSpectral_berggrenInvGenAction_injective

/-!
# Berggren Spectral Theory on Finite Quotients

This file develops the spectral theory of the Berggren averaging operator
on the isotropic cone of the Lorentzian quadratic form Q(x,y,z) = x² + y² - z²
reduced modulo odd primes q.

## Main Results

### Algebraic Infrastructure (over ℤ)
* `berggrenGen_preserves_metric` — Each generator preserves the Lorentz metric MᵀQM = Q.
* `berggrenGen_mul_inv` / `berggrenInvGen_mul_gen` — Verified inverse pairs.
* `berggren_sum_lorentz_identity` — SᵀQS = diag(1,1,-9), the key amplification identity.

### Mod-q Reduction
* `quadFormMod_preserved_by_gen` — Generators preserve the quadratic form mod q.
* `berggrenGenAction` — The action on the isotropic cone is well-defined.
* `berggrenGenAction_bijective` — Each generator acts by bijection on the finite cone.

### Operator Theory
* `berggren_constants_eigenvalue_one` — Constants are eigenvectors with eigenvalue 1.
* `berggren_mean_zero_invariant` — The averaging operator preserves mean-zero functions.
* `berggren_averaging_sum_preserved` — Total sums are preserved by the operator.
-/

set_option maxHeartbeats 800000

open Matrix Finset BigOperators

open BerggrenFiniteSpectral

/-! ## §1. Core Definitions over ℤ -/






/-! ## §2. Algebraic Identities -/









/-! ## §3. Quadratic Form Preservation over ℤ -/



/-! ## §4. Mod-q Definitions and Form Preservation -/









/-! ## §5. Isotropic Cone and Group Action -/








/-- The inverse generator action is bijective on finite isotropic cones. -/
theorem berggrenInvGenAction_bijective (q : ℕ) [NeZero q]
    [Fintype (IsotropicNonzero q)] (i : Fin 3) :
    Function.Bijective (berggrenInvGenAction q i) :=
  (Finite.injective_iff_bijective).mp (berggrenInvGenAction_injective q i)

/-! ## §6. Averaging Operator -/



/-! ## §7. Constants are Eigenvectors -/



/-! ## §8. Mean-Zero Invariance -/



/-! ## §9. Norm Bounds -/



/-! ## §10. Seed Triple Computations -/






/-! ## §11. Sum Operator on the Pythagorean Light Cone -/


/-! ## §12. Cross-Generator Lorentz Products -/




/-! ## §13. Trace Structure -/





open BerggrenFiniteSpectral in
theorem solution(q : ℕ) [NeZero q]
    [Fintype (IsotropicNonzero q)] [DecidableEq (IsotropicNonzero q)]
    (f : IsotropicNonzero q → ℂ) :
    ∑ x, berggrenAveragingOp q f x = ∑ x, f x := by
  simp only [berggrenAveragingOp, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Finset.mul_sum]
  simp_rw [Fin.sum_univ_three, Finset.sum_add_distrib]
  -- Each inverse generator acts by bijection, so summing over its image = summing over all
  have h0 : ∑ x, f (berggrenInvGenAction q 0 x) = ∑ x, f x :=
    Fintype.sum_bijective _ (berggrenInvGenAction_bijective q 0) _ _ (fun _ => rfl)
  have h1 : ∑ x, f (berggrenInvGenAction q 1 x) = ∑ x, f x :=
    Fintype.sum_bijective _ (berggrenInvGenAction_bijective q 1) _ _ (fun _ => rfl)
  have h2 : ∑ x, f (berggrenInvGenAction q 2 x) = ∑ x, f x :=
    Fintype.sum_bijective _ (berggrenInvGenAction_bijective q 2) _ _ (fun _ => rfl)
  rw [h0, h1, h2]
  ring
