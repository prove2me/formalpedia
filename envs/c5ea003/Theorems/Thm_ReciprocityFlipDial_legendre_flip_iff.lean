-- Prove2me | Theorems.Thm_ReciprocityFlipDial_legendre_flip_iff
-- name    : ReciprocityFlipDial.legendre_flip_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:56:00.186799+00:00
-- url     : https://prove2.me/theorems/d329c1ae-c821-4812-b964-0a11a2431f2e
-- title:
--   The sharp dichotomy.
-- statement:
--   **The sharp dichotomy.**  For distinct odd primes the two dial forms flip
--   sign *iff* both primes are `3 mod 4`; there is no other source of disagreement.
--
--   ```lean
--   theorem ReciprocityFlipDial.legendre_flip_iff[Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
--       (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
--       (legendreSym q p = - legendreSym p q) ↔ (p % 4 = 3 ∧ q % 4 = 3) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ReciprocityFlipDial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ReciprocityFlipDial.lean#L126

-- Thm stub generated from Algebra/ReciprocityFlipDial.lean
import Mathlib
import Definitions.Def_Algebra_ReciprocityFlipDial
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

open ReciprocityFlipDial

open Finset

/-! ## 1. The twist character -/







/-! ## 2. The prime-bottom (Legendre) dichotomy -/

variable {p q : ℕ}

theorem ReciprocityFlipDial.legendre_flip_iff[Fact (Nat.Prime p)] [Fact (Nat.Prime q)]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    (legendreSym q p = - legendreSym p q) ↔ (p % 4 = 3 ∧ q % 4 = 3) := by sorry
