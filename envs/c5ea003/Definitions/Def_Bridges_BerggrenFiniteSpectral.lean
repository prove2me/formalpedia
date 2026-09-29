-- Prove2me | Definitions.Def_Bridges_BerggrenFiniteSpectral
-- name    : Bridges_BerggrenFiniteSpectral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:24:51.598176+00:00
-- url     : https://prove2.me/theorems/5a95865b-5486-493e-bbf6-cf93157d9a28
-- title:
--   Aether Catalog definitions — Bridges_BerggrenFiniteSpectral
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenFiniteSpectral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenFiniteSpectral.lean by skeleton subtraction
import Mathlib

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

namespace BerggrenFiniteSpectral

/-! ## §1. Core Definitions over ℤ -/

/-- The Lorentz metric matrix Q = diag(1, 1, -1). -/
def metricQ : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- The three Berggren generators. -/
def berggrenGen : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ
  | 0 => !![1, -2, 2; 2, -1, 2; 2, -2, 3]
  | 1 => !![1, 2, 2; 2, 1, 2; 2, 2, 3]
  | 2 => !![-1, 2, 2; -2, 1, 2; -2, 2, 3]

/-- The three Berggren inverse generators. -/
def berggrenInvGen : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ
  | 0 => !![1, 2, -2; -2, -1, 2; -2, -2, 3]
  | 1 => !![1, 2, -2; 2, 1, -2; -2, -2, 3]
  | 2 => !![-1, -2, 2; 2, 1, -2; -2, -2, 3]

/-- The Lorentzian quadratic form Q(v) = v₀² + v₁² - v₂². -/
def quadForm (v : Fin 3 → ℤ) : ℤ := v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2

/-- Sum of the three Berggren generators. -/
def berggrenSum : Matrix (Fin 3) (Fin 3) ℤ :=
  berggrenGen 0 + berggrenGen 1 + berggrenGen 2

/-! ## §2. Algebraic Identities -/



/-- Generator times its inverse is the identity. -/
theorem berggrenGen_mul_inv (i : Fin 3) :
    berggrenGen i * berggrenInvGen i = 1 := by
  fin_cases i <;> decide

/-- Inverse times generator is the identity. -/
theorem berggrenInvGen_mul_gen (i : Fin 3) :
    berggrenInvGen i * berggrenGen i = 1 := by
  fin_cases i <;> decide





/-! ## §3. Quadratic Form Preservation over ℤ -/



/-! ## §4. Mod-q Definitions and Form Preservation -/

/-- The quadratic form over ZMod q. -/
def quadFormMod (q : ℕ) (v : Fin 3 → ZMod q) : ZMod q :=
  v 0 * v 0 + v 1 * v 1 - v 2 * v 2

/-- The Berggren generators reduced mod q. -/
def berggrenGenMod (q : ℕ) : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod q) :=
  fun i => (berggrenGen i).map (Int.castRingHom (ZMod q))

/-- The Berggren inverse generators reduced mod q. -/
def berggrenInvGenMod (q : ℕ) : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod q) :=
  fun i => (berggrenInvGen i).map (Int.castRingHom (ZMod q))

private theorem map_int_mul_eq {q : ℕ} [NeZero q] (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (h : A * B = 1) :
    A.map (Int.castRingHom (ZMod q)) * B.map (Int.castRingHom (ZMod q)) = 1 := by
  rw [← Matrix.map_mul, h]
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs with h <;> simp

/-- Generator mod q times its inverse mod q is the identity. -/
theorem berggrenGenMod_mul_inv (q : ℕ) [NeZero q] (i : Fin 3) :
    berggrenGenMod q i * berggrenInvGenMod q i = 1 :=
  map_int_mul_eq (berggrenGen i) (berggrenInvGen i) (berggrenGen_mul_inv i)

/-- Inverse mod q times generator mod q is the identity. -/
theorem berggrenInvGenMod_mul_gen (q : ℕ) [NeZero q] (i : Fin 3) :
    berggrenInvGenMod q i * berggrenGenMod q i = 1 :=
  map_int_mul_eq (berggrenInvGen i) (berggrenGen i) (berggrenInvGen_mul_gen i)

/-- The quadratic form is preserved by Berggren generators mod q. -/
theorem quadFormMod_preserved_by_gen (q : ℕ) [NeZero q] (i : Fin 3)
    (v : Fin 3 → ZMod q) :
    quadFormMod q ((berggrenGenMod q i).mulVec v) = quadFormMod q v := by
  simp only [quadFormMod]
  fin_cases i <;> {
    simp [berggrenGenMod, berggrenGen, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.map_apply]
    ring
  }

/-- The quadratic form is preserved by Berggren inverse generators mod q. -/
theorem quadFormMod_preserved_by_invGen (q : ℕ) [NeZero q] (i : Fin 3)
    (v : Fin 3 → ZMod q) :
    quadFormMod q ((berggrenInvGenMod q i).mulVec v) = quadFormMod q v := by
  simp only [quadFormMod]
  fin_cases i <;> {
    simp [berggrenInvGenMod, berggrenInvGen, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.map_apply]
    ring
  }

/-! ## §5. Isotropic Cone and Group Action -/

/-- A nonzero isotropic vector mod q. -/
def IsotropicNonzero (q : ℕ) :=
  {v : Fin 3 → ZMod q // quadFormMod q v = 0 ∧ v ≠ 0}

/-- Applying an invertible matrix to a nonzero vector gives a nonzero vector. -/
private theorem mulVec_ne_zero_of_inv {q : ℕ} [NeZero q]
    (M Minv : Matrix (Fin 3) (Fin 3) (ZMod q)) (hinv : Minv * M = 1)
    (v : Fin 3 → ZMod q) (hv : v ≠ 0) :
    M.mulVec v ≠ 0 := by
  intro h
  apply hv
  have : Minv.mulVec (M.mulVec v) = Minv.mulVec 0 := by rw [h]
  rw [Matrix.mulVec_mulVec, hinv, Matrix.mulVec_zero] at this
  simpa using this

/-- The Berggren generator action on the isotropic cone is well-defined. -/
def berggrenGenAction (q : ℕ) [NeZero q] (i : Fin 3) (v : IsotropicNonzero q) :
    IsotropicNonzero q :=
  ⟨(berggrenGenMod q i).mulVec v.1,
    ⟨by rw [quadFormMod_preserved_by_gen]; exact v.2.1,
     mulVec_ne_zero_of_inv _ _ (berggrenInvGenMod_mul_gen q i) _ v.2.2⟩⟩

/-- The Berggren inverse generator action on the isotropic cone is well-defined. -/
def berggrenInvGenAction (q : ℕ) [NeZero q] (i : Fin 3) (v : IsotropicNonzero q) :
    IsotropicNonzero q :=
  ⟨(berggrenInvGenMod q i).mulVec v.1,
    ⟨by rw [quadFormMod_preserved_by_invGen]; exact v.2.1,
     mulVec_ne_zero_of_inv _ _ (berggrenGenMod_mul_inv q i) _ v.2.2⟩⟩





/-! ## §6. Averaging Operator -/

/-- The Berggren averaging operator T_q on functions f : IsotropicNonzero q → ℂ.
    T_q f(x) = (1/3)(f(B₁⁻¹ x) + f(B₂⁻¹ x) + f(B₃⁻¹ x)). -/
noncomputable def berggrenAveragingOp (q : ℕ) [NeZero q] :
    (IsotropicNonzero q → ℂ) →ₗ[ℂ] (IsotropicNonzero q → ℂ) where
  toFun f x := (1 / 3 : ℂ) * ∑ i : Fin 3, f (berggrenInvGenAction q i x)
  map_add' f g := by
    ext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

/-- The mean-zero subspace: functions whose sum over all isotropic vectors is zero. -/
noncomputable def meanZeroSubspace (q : ℕ) [NeZero q] [Fintype (IsotropicNonzero q)] :
    Submodule ℂ (IsotropicNonzero q → ℂ) where
  carrier := {f | ∑ x : IsotropicNonzero q, f x = 0}
  add_mem' {f g} hf hg := by
    change ∑ x, (f x + g x) = 0
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  zero_mem' := by simp
  smul_mem' c f hf := by
    show ∑ x, (c • f) x = 0
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [show ∑ x, f x = 0 from hf, mul_zero]

/-! ## §7. Constants are Eigenvectors -/



/-! ## §8. Mean-Zero Invariance -/



/-! ## §9. Norm Bounds -/

/-- The ℓ² norm squared of a function on the isotropic cone. -/
noncomputable def l2NormSq (q : ℕ) [NeZero q] [Fintype (IsotropicNonzero q)]
    (f : IsotropicNonzero q → ℂ) : ℝ :=
  ∑ x : IsotropicNonzero q, ‖f x‖ ^ 2


/-! ## §10. Seed Triple Computations -/






/-! ## §11. Sum Operator on the Pythagorean Light Cone -/


/-! ## §12. Cross-Generator Lorentz Products -/




/-! ## §13. Trace Structure -/




end BerggrenFiniteSpectral


