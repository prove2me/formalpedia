-- Prove2me | Definitions.Def_Evergreen_QuaternionFactoring_QuaternionFactoring
-- name    : Evergreen_QuaternionFactoring_QuaternionFactoring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:38:40.659984+00:00
-- url     : https://prove2.me/theorems/7731ec5a-9dbd-441d-a34e-e827c75952ba
-- title:
--   Aether Catalog definitions — Evergreen_QuaternionFactoring_QuaternionFactoring
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.QuaternionFactoring.QuaternionFactoring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/QuaternionFactoring/QuaternionFactoring.lean by skeleton subtraction
import Mathlib

/-!
# Quaternion Factoring: From Pythagorean Quadruples to Integer Factorization

## Overview

This file formalizes the core algebraic connection between quaternion arithmetic
and integer factoring. The key insight is that factoring N into primes corresponds
to decomposing a quaternion of norm N into a product of prime-norm quaternions.

## Mathematical Background

The **Hurwitz quaternions** ℤ[i,j,k] = {a + bi + cj + dk : a,b,c,d ∈ ℤ} form
a non-commutative ring with a Euclidean norm N(q) = a² + b² + c² + d².

**Jacobi's Four-Square Theorem** states that every positive integer can be
written as a sum of four squares. Combined with norm multiplicativity, this
means every positive integer is the norm of some quaternion, and composite
integers correspond to quaternion products.

## Main Results

- `sum_four_squares_exists`: Every natural number is a sum of four squares (statement)
- `quaternion_product_formula`: Explicit product formula for quaternion multiplication
- `norm_prime_decomposition`: If N = p·q, decomposition into norm-p and norm-q quaternions
- `sl2z_action_on_params`: SL(2,ℤ) acts on quadruple parameters preserving the norm
-/

/-! ## Section 1: Quaternion Algebra over ℤ -/

/-- An integer quaternion (a, b, c, d) represents a + bi + cj + dk. -/
structure IntQuaternion where
  re : ℤ
  im_i : ℤ
  im_j : ℤ
  im_k : ℤ
  deriving Repr, DecidableEq

namespace IntQuaternion

/-- The norm of an integer quaternion: N(q) = a² + b² + c² + d². -/
def norm (q : IntQuaternion) : ℤ :=
  q.re^2 + q.im_i^2 + q.im_j^2 + q.im_k^2

/-- Quaternion multiplication (non-commutative). -/
def mul (q₁ q₂ : IntQuaternion) : IntQuaternion where
  re   := q₁.re * q₂.re - q₁.im_i * q₂.im_i - q₁.im_j * q₂.im_j - q₁.im_k * q₂.im_k
  im_i := q₁.re * q₂.im_i + q₁.im_i * q₂.re + q₁.im_j * q₂.im_k - q₁.im_k * q₂.im_j
  im_j := q₁.re * q₂.im_j - q₁.im_i * q₂.im_k + q₁.im_j * q₂.re + q₁.im_k * q₂.im_i
  im_k := q₁.re * q₂.im_k + q₁.im_i * q₂.im_j - q₁.im_j * q₂.im_i + q₁.im_k * q₂.re

/-- Quaternion conjugate. -/
def conj (q : IntQuaternion) : IntQuaternion where
  re   := q.re
  im_i := -q.im_i
  im_j := -q.im_j
  im_k := -q.im_k

/-
The norm is multiplicative: N(q₁ · q₂) = N(q₁) · N(q₂).
-/

/-
The norm is always nonnegative.
-/

/-
The norm is zero iff the quaternion is zero.
-/

/-
q · conj(q) = norm(q) · 1.
-/

end IntQuaternion

/-! ## Section 2: SL(2,ℤ) Action on Quadruple Parameters -/


/-
The generator T : (m,n,p,q) ↦ (m+n,n,p,q) preserves the
    quadruple structure (though not the norm).
-/

/-! ## Section 3: Sum of Four Squares -/

/-
Lagrange's four-square theorem (statement only — deep result).
-/

/-! ## Section 4: GCD Factor Extraction -/

/-
If we find a short vector (x,y,z) in L₄(N), then gcd(x²+y²+z², N)
    may reveal a factor. This formalizes the extraction step.
-/


