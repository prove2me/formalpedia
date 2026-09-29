-- Prove2me | Definitions.Def_Algebra_ReciprocityFlipDial
-- name    : Algebra_ReciprocityFlipDial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:48:48.044727+00:00
-- url     : https://prove2.me/theorems/3069e435-4aa2-4d10-a0bc-a69e7a0c6c71
-- title:
--   Aether Catalog definitions — Algebra_ReciprocityFlipDial
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ReciprocityFlipDial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ReciprocityFlipDial.lean by skeleton subtraction
import Mathlib
/-
# Reciprocity-Flip Dials: the sign artifact behind the paper-226 secondaries

Formal core of experiment **577** (paper 227), diagnostic part (1).

## Background

A *dial* attaches to an integer `N` a vector of quadratic symbols recording, for
each small prime `ℓ`, whether `N` is a quadratic residue mod `ℓ`.  Two
implementations were used in the experimental record:

* the **clean (Legendre) form**  `ℓ ↦ (N | ℓ)`  — symbol with the *prime on the
  bottom*;
* the **product / composite-bottom form** `ℓ ↦ (ℓ | N)` — symbol with the
  *composite* `N` on the bottom, evaluated as a Jacobi symbol.

Experimentally the second form was much weaker as a covariate, and the diagnosis
was that the two forms differ by a **reciprocity sign flip** that switches on
exactly when `ℓ ≡ 3 (mod 4)` and `N ≡ 3 (mod 4)` — reported as "conditional flip
100%, 2680/2680, zero violations".

This file proves that diagnosis, in both the prime-bottom (Legendre) and
composite-bottom (Jacobi) settings, and derives the exact residue bookkeeping
that turns the conditional statement into an unconditional density.

## Main results

* `ReciprocityFlipDial.legendre_flip_of_three_mod_four` — the flip is *total*
  on its condition: for distinct odd primes `p ≡ q ≡ 3 (mod 4)` the two dial
  forms are exact negatives (zero violations).
* `ReciprocityFlipDial.legendre_agree_of_not_both_three_mod_four` — off the
  condition the two forms *agree identically*.
* `ReciprocityFlipDial.legendre_flip_iff` — the sharp dichotomy: the dials flip
  **iff** both primes are `3 mod 4`.
* `ReciprocityFlipDial.jacobi_flip_iff_of_coprime` — the same dichotomy for the
  composite-bottom (Jacobi) dial actually used in the experiment.
* `ReciprocityFlipDial.twist_mul_self`, `ReciprocityFlipDial.jacobi_eq_twist_mul` —
  the flipped form is the clean form multiplied by a `± 1` **twist character**
  depending only on `(ℓ mod 4, N mod 4)`; the twist is an involution, so no
  information is destroyed pointwise, only *linearly* scrambled.
* `ReciprocityFlipDial.twist_sum_eq_zero`, `ReciprocityFlipDial.twist_density` —
  the twist has mean zero over the odd residues mod 4 for a fixed `ℓ ≡ 3 mod 4`,
  and fires on exactly one of the four odd residue pairs (the `25%`
  unconditional rate that the experiment measured after conditioning).
* `ReciprocityFlipDial.dial_twist_scrambles` — a concrete linear-algebra
  consequence: a clean dial that is perfectly correlated with a target can have
  its flipped form *exactly uncorrelated* with the same target.  This is the
  formal content of "the published weakness is a dial-form artifact".
-/

namespace ReciprocityFlipDial

open Finset

/-! ## 1. The twist character -/

/-- The reciprocity **twist**: `twist a b = -1` exactly when both `a` and `b` are
`3 mod 4`, and `+1` otherwise.  It is defined on residues mod `4`. -/
def twist (a b : ℕ) : ℤ := if a % 4 = 3 ∧ b % 4 = 3 then -1 else 1






/-! ## 2. The prime-bottom (Legendre) dichotomy -/

variable {p q : ℕ}





/-! ## 3. The composite-bottom (Jacobi) dial -/





/-! ## 4. Residue bookkeeping: the unconditional flip density -/

/-- The odd residues mod `4`. -/
def oddRes : Finset ℕ := {1, 3}



/-! ## 5. The artifact: a twist can annihilate a perfect correlation -/


end ReciprocityFlipDial


