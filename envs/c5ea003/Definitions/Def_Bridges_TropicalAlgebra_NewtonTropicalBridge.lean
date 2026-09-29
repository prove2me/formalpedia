-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_NewtonTropicalBridge
-- name    : Bridges_TropicalAlgebra_NewtonTropicalBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:19.32799+00:00
-- url     : https://prove2.me/theorems/1182090e-6433-468b-819c-4febd1cb4e48
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_NewtonTropicalBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.NewtonTropicalBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/NewtonTropicalBridge.lean by skeleton subtraction
import Mathlib
/-
  # Newton–Tropical Bridge:
  # Polynomial Valuation Profiles, Tropical Evaluation,
  # and Cryptographic Root Certificates

  ## Domain Bridge: Number Theory ↔ Tropical Geometry ↔ Cryptography

  The Newton polygon of a polynomial f(x) = ∑ aᵢxⁱ with respect to a
  p-adic valuation v is encoded by the **valuation profile** i ↦ v(aᵢ).
  The **tropical evaluation** of this profile at a point t ∈ ℕ∞ is
    T_f(t) = inf_i (v(aᵢ) + i · t)
  which is the lower envelope of the Newton polygon.

  ## Main Results

  1. `NewtonProfile` — novel structure: the valuation profile of a polynomial
  2. `tropicalEval` — tropical polynomial evaluation (lower envelope)
  3. `tropicalEval_at_zero` — evaluation at zero gives min coefficient valuation
  4. `tropicalEval_min_le` — min of profiles dominates eval of min profile
  5. `tropical_eval_at_root_le` — bridge theorem: v(f(a)) ≥ T_f(v(a))
  6. `NewtonSlopeCertificate` — cryptographic certificate structure
  7. `tropicalEval_stable` — stability under profile perturbation
  8. `dominant_lt_nondominant` — dominant term analysis
-/


open Finset BigOperators WithTop

noncomputable section

namespace NewtonTropicalBridge

/-! ## §1. Newton Valuation Profile -/

/-- A **Newton valuation profile** of degree `n`: the map i ↦ v(aᵢ) ∈ ℕ∞
for a polynomial f(x) = a₀ + a₁x + ... + aₙxⁿ under some valuation v. -/
structure NewtonProfile (n : ℕ) where
  /-- The valuation of each coefficient -/
  profile : Fin (n + 1) → ℕ∞
  /-- At least one coefficient has finite valuation -/
  nonzero : ∃ i, profile i ≠ ⊤

/-- Construct a Newton profile from polynomial coefficients and a valuation. -/
def NewtonProfile.ofCoeffs {R : Type*} [CommMonoidWithZero R] [Add R]
    {n : ℕ} (coeffs : Fin (n + 1) → R) (v : R → ℕ∞)
    (_hv0 : v 0 = ⊤) (hnz : ∃ i, v (coeffs i) ≠ ⊤) :
    NewtonProfile n where
  profile := fun i => v (coeffs i)
  nonzero := hnz

/-! ## §2. Tropical Polynomial Evaluation -/

/-- **Tropical polynomial evaluation**: inf_i (profileᵢ + i · t).
This is the lower envelope of the Newton polygon. -/
def tropicalEval {n : ℕ} (vp : NewtonProfile n) (t : ℕ∞) : ℕ∞ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => vp.profile i + (i : ℕ) * t)

/-! ## §3. Properties of Tropical Evaluation -/



/-! ## §4. Dominant Term Analysis -/

/-- A term i is **dominant** at point t if it achieves the infimum. -/
def isDominantTerm {n : ℕ} (vp : NewtonProfile n) (t : ℕ∞) (i : Fin (n + 1)) : Prop :=
  vp.profile i + (i : ℕ) * t = tropicalEval vp t



/-! ## §5. Profile Operations -/

/-- **Pointwise minimum** of two profiles. -/
def profileMin {n : ℕ} (pA pB : NewtonProfile n) : NewtonProfile n where
  profile := fun i => min (pA.profile i) (pB.profile i)
  nonzero := by
    obtain ⟨i, hi⟩ := pA.nonzero
    exact ⟨i, fun h => hi (eq_top_mono (min_le_left _ _) h)⟩


/-! ## §6. Root–Valuation Bridge Theorem -/

/-
Helper: v(aⁿ) = n · v(a) for multiplicative valuations.
-/

/-
**Root–Valuation Bridge**: v(∑ cᵢ · aⁱ) ≥ T_profile(v(a)).
The p-adic valuation of a polynomial value is bounded below by
the tropical evaluation of the Newton profile.
-/

/-! ## §7. Stability of Tropical Evaluation -/

/-- Two profiles are **ε-close** if valuations differ by at most ε. -/
def profileClose {n : ℕ} (pA pB : NewtonProfile n) (ε : ℕ) : Prop :=
  ∀ i, pA.profile i ≤ pB.profile i + ε ∧ pB.profile i ≤ pA.profile i + ε

/-
**Stability**: ε-close profiles have tropical evaluations within ε.
-/

/-! ## §8. Newton Slope Certificate -/

/-- A **Newton slope certificate** certifies v_p(f(a)) ≥ B using
only the Newton polygon data and v(a). Zero-knowledge-friendly. -/
structure NewtonSlopeCertificate (n : ℕ) where
  profile : NewtonProfile n
  pointVal : ℕ∞
  bound : ℕ∞
  tropical_bound : bound ≤ tropicalEval profile pointVal



/-! ## §9. Valued Polynomial Structure -/

/-- A polynomial over a valued ring, packaging coefficients with valuation. -/
structure ValuedPolynomial (R : Type*) [CommSemiring R] (n : ℕ) where
  coeffs : Fin (n + 1) → R
  valuation : R → ℕ∞
  val_zero : valuation 0 = ⊤
  val_mul : ∀ a b, valuation (a * b) = valuation a + valuation b
  val_one : valuation 1 = 0
  val_ultra : ∀ a b, min (valuation a) (valuation b) ≤ valuation (a + b)
  nonzero : ∃ i, valuation (coeffs i) ≠ ⊤

/-- Extract the Newton profile from a valued polynomial. -/
def ValuedPolynomial.newtonProfile {R : Type*} [CommSemiring R]
    {n : ℕ} (fp : ValuedPolynomial R n) : NewtonProfile n :=
  NewtonProfile.ofCoeffs fp.coeffs fp.valuation fp.val_zero fp.nonzero

/-- Evaluate a valued polynomial at a point. -/
def ValuedPolynomial.eval {R : Type*} [CommSemiring R]
    {n : ℕ} (fp : ValuedPolynomial R n) (a : R) : R :=
  ∑ i : Fin (n + 1), fp.coeffs i * a ^ (i : ℕ)


/-! ## §10. Tropical Discriminant -/

/-- The **tropical discriminant** of a degree-2 profile:
min(2·v(b), v(a) + v(c)) for ax² + bx + c. -/
def tropDiscriminant2 (vp : NewtonProfile 2) : ℕ∞ :=
  min (2 * vp.profile ⟨1, by omega⟩)
      (vp.profile ⟨0, by omega⟩ + vp.profile ⟨2, by omega⟩)


/-! ## §11. Infimal Convolution (Tropical Product) -/

/-- **Infimal convolution**: the tropical product of two profiles.
For degree-m and degree-n profiles, entry k = inf_{i+j=k}(pA_i + pB_j). -/
def infimalConvolution {m n : ℕ} (pA : Fin (m + 1) → ℕ∞) (pB : Fin (n + 1) → ℕ∞) :
    Fin (m + n + 1) → ℕ∞ :=
  fun k => Finset.univ.inf' Finset.univ_nonempty
    (fun ij : Fin (m + 1) × Fin (n + 1) =>
      if (ij.1 : ℕ) + (ij.2 : ℕ) = (k : ℕ)
      then pA ij.1 + pB ij.2
      else ⊤)

/-
The infimal convolution at k = 0 is bounded by pA(0) + pB(0).
-/

/-! ## §12. Falsifiable Conjecture -/

 -- Full statement requires p-adic root theory

/-! ## §13. Computational Helpers -/


end NewtonTropicalBridge


