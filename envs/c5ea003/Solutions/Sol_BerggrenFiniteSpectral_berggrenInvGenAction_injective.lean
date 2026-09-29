-- Prove2me | solution 1 for BerggrenFiniteSpectral.berggrenInvGenAction_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:08:18.827747+00:00
-- url     : https://prove2.me/submissions/3bc9a381-0480-4656-b93e-c227bd83b10f

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
    Function.Injective (berggrenInvGenAction q i) := by
  intro ⟨v, hv⟩ ⟨w, hw⟩ h
  have hinj : (berggrenInvGenMod q i).mulVec v = (berggrenInvGenMod q i).mulVec w :=
    congrArg Subtype.val h
  apply Subtype.ext
  have hinv := berggrenGenMod_mul_inv q i
  calc v = (1 : Matrix _ _ _).mulVec v := by simp
    _ = (berggrenGenMod q i * berggrenInvGenMod q i).mulVec v := by rw [hinv]
    _ = (berggrenGenMod q i).mulVec ((berggrenInvGenMod q i).mulVec v) := by
        rw [Matrix.mulVec_mulVec]
    _ = (berggrenGenMod q i).mulVec ((berggrenInvGenMod q i).mulVec w) := by rw [hinj]
    _ = (berggrenGenMod q i * berggrenInvGenMod q i).mulVec w := by
        rw [Matrix.mulVec_mulVec]
    _ = (1 : Matrix _ _ _).mulVec w := by rw [hinv]
    _ = w := by simp
