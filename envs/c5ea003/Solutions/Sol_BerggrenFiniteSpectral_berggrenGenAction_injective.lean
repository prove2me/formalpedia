-- Prove2me | solution 1 for BerggrenFiniteSpectral.berggrenGenAction_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:08:18.237385+00:00
-- url     : https://prove2.me/submissions/3225ce82-591b-4afd-bdbe-5d17c49e7a10

-- Sol generated from Bridges/BerggrenFiniteSpectral.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenFiniteSpectral

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









/-! ## §6. Averaging Operator -/



/-! ## §7. Constants are Eigenvectors -/



/-! ## §8. Mean-Zero Invariance -/



/-! ## §9. Norm Bounds -/



/-! ## §10. Seed Triple Computations -/






/-! ## §11. Sum Operator on the Pythagorean Light Cone -/


/-! ## §12. Cross-Generator Lorentz Products -/




/-! ## §13. Trace Structure -/





open BerggrenFiniteSpectral in
theorem solution(q : ℕ) [NeZero q] (i : Fin 3) :
    Function.Injective (berggrenGenAction q i) := by
  intro ⟨v, hv⟩ ⟨w, hw⟩ h
  have hinj : (berggrenGenMod q i).mulVec v = (berggrenGenMod q i).mulVec w :=
    congrArg Subtype.val h
  apply Subtype.ext
  have hinv := berggrenInvGenMod_mul_gen q i
  calc v = (1 : Matrix _ _ _).mulVec v := by simp
    _ = (berggrenInvGenMod q i * berggrenGenMod q i).mulVec v := by rw [hinv]
    _ = (berggrenInvGenMod q i).mulVec ((berggrenGenMod q i).mulVec v) := by
        rw [Matrix.mulVec_mulVec]
    _ = (berggrenInvGenMod q i).mulVec ((berggrenGenMod q i).mulVec w) := by rw [hinj]
    _ = (berggrenInvGenMod q i * berggrenGenMod q i).mulVec w := by
        rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix _ _ _).mulVec w := by rw [hinv]
    _ = w := by simp
