-- Prove2me | Definitions.Def_Cryptography_LWE_SearchDecisionCore
-- name    : Cryptography_LWE_SearchDecisionCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:39:05.60901+00:00
-- url     : https://prove2.me/theorems/f88bb784-2b9b-4794-a050-cda25fd2b92a
-- title:
--   Aether Catalog definitions — Cryptography_LWE_SearchDecisionCore
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LWE.SearchDecisionCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LWE/SearchDecisionCore.lean by skeleton subtraction
import Mathlib

/-!
# LWE Search-to-Decision Reduction: Algebraic Core

This module formalizes the key algebraic and analytic ingredients underlying
the search-to-decision reduction for the Learning with Errors problem.

## Mathematical Background

The LWE search-to-decision reduction (Regev 2005, Peikert 2009) reduces
distinguishing LWE samples from uniform to recovering the secret vector.
The reduction proceeds coordinate-by-coordinate: for prime modulus q,
one can guess each coordinate of the secret and verify correctness using
the algebraic structure of ℤ_q as a field.

The core algebraic fact is that for prime q, affine maps x ↦ ax + b
are bijections on ℤ_q when a ≠ 0. This ensures that rerandomizing an
LWE sample by an affine transformation preserves uniformity on the
"wrong guess" side of the hybrid argument.

## Main Results

1. `ZMod.affine_bijective` — Affine maps are bijections over ℤ_p (p prime)
2. `noise_accumulation_bound` — Accumulated noise from m LWE samples ≤ mB
3. `regev_rounding_bit1` — Rounding-based decryption works when |e| < q/4
4. `search_to_decision_advantage_bound` — Advantage loss factor of n

## References

* Regev, "On Lattices, Learning with Errors, Random Linear Codes,
  and Cryptography", STOC 2005 / JACM 2009
* Peikert, "Public-Key Cryptosystems from the Worst-Case Shortest
  Vector Problem", STOC 2009
-/

open Finset BigOperators Real

noncomputable section

/-! ## Section 1: Affine Bijections over ℤ_p -/

-- !-- The key algebraic fact: for prime p, multiplication by a nonzero
-- element is injective (hence bijective on a finite type). This is
-- because ℤ_p is a field when p is prime. Combined with the bijection
-- of translation, affine maps are bijections. -- !--

/-- **Multiplication by a nonzero element is bijective over ℤ_p** (p prime). -/
theorem ZMod.mul_left_bijective_of_prime {p : ℕ} [Fact (Nat.Prime p)]
    (a : ZMod p) (ha : a ≠ 0) :
    Function.Bijective (fun x : ZMod p => a * x) :=
  (mul_right_injective₀ ha).bijective_of_finite

/-- **Affine maps are bijections over ℤ_p** (p prime, a ≠ 0).

This is the algebraic core of the LWE search-to-decision reduction:
when rerandomizing an LWE sample (a, b) by an affine transformation
on the "a" component, the uniformity of "a" is preserved. -/
theorem ZMod.affine_bijective {p : ℕ} [Fact (Nat.Prime p)]
    (a b : ZMod p) (ha : a ≠ 0) :
    Function.Bijective (fun x : ZMod p => a * x + b) :=
  (AddGroup.addRight_bijective b).comp
    (ZMod.mul_left_bijective_of_prime a ha)

/-- **Affine map as an equivalence** (bundled version). -/
def ZMod.affineEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (a b : ZMod p) (ha : a ≠ 0) : ZMod p ≃ ZMod p :=
  Equiv.ofBijective _ (ZMod.affine_bijective a b ha)

/-
**The inverse of an affine map is affine**.
If f(x) = ax + b, then f⁻¹(y) = a⁻¹(y - b).
-/




/-! ## Section 2: Noise Accumulation Bounds -/

-- !-- In Regev's encryption, ciphertext noise = subset sum of LWE errors.
-- The accumulated noise is bounded by (subset size) × (per-sample bound). -- !--




/-! ## Section 3: Regev Encryption Rounding Correctness -/

-- !-- Regev's encryption encodes bit μ ∈ {0,1} as μ · (q/2).
-- Decryption checks which "half" of [0,q) the noisy value falls in.
-- Correctness requires accumulated noise |e| < q/4. -- !--





/-! ## Section 4: Search-to-Decision Advantage Bound -/

-- !-- The search-to-decision reduction decomposes total advantage δ
-- into n coordinate contributions via a hybrid argument. By pigeonhole,
-- at least one coordinate contributes ≥ δ/n. -- !--



/-! ## Section 5: Modulus Switching -/



/-! ## Section 6: Advantage Amplification -/


/-! ## Section 7: Modulus-Noise Tradeoff -/


end

/-! ## Axiom verification -/


