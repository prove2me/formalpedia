-- Prove2me | Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
-- name    : Applications_CyclicCubicTypeChannel_Splitting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:40:08.434147+00:00
-- url     : https://prove2.me/theorems/7e9d7ee8-2264-4964-96a7-1ee00b7bb6c5
-- title:
--   Aether Catalog definitions — Applications_CyclicCubicTypeChannel_Splitting
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CyclicCubicTypeChannel.Splitting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CyclicCubicTypeChannel/Splitting.lean by skeleton subtraction
import Mathlib
/-
# The cyclic cubic field `ℚ(ζ₇ + ζ₇⁻¹)` has exactly two splitting types

## Context (FACT round-32 #3, "THE-CYCLIC-CUBIC-IS-FULLY-PINNED", paper 122)

The real subfield `K = ℚ(ζ₇ + ζ₇⁻¹)` of the seventh cyclotomic field is the
cyclic cubic field of conductor `7`.  Its ring of integers is `ℤ[α]` with
`α = ζ₇ + ζ₇⁻¹` a root of

  `f(X) = X³ + X² − 2X − 1`      (discriminant `49`).

By Dedekind's factorisation criterion the splitting type of an unramified
rational prime `p ≠ 7` in `K` is read off from the factorisation of `f mod p`.
This file proves, from scratch and with no number-field machinery, the complete
arithmetic law behind the experiment:

* `CyclicCubic.root_iff` — for a prime `p ≠ 7`, `f` has a root in `ZMod p`
  **iff** `p ≡ ±1 (mod 7)`;
* `CyclicCubic.splits_completely` — one root forces three *distinct* roots
  (the map `x ↦ x² − 2` cycles them), so `f mod p` either splits completely or
  is irreducible: **only two types**;
* `CyclicCubic.irreducible_mod_of_not_pm_one` — the inert case;
* `CyclicCubic.resDeg_congr` — the residue degree is a function of `p mod 7`
  alone: the arithmetic form of **full pinning**;
* `CyclicCubic.irreducible_rat`, `CyclicCubic.minpoly_zeta_add_inv` — `f` is
  irreducible over `ℚ` and is the minimal polynomial of `ζ₇ + ζ₇⁻¹`, so `K`
  really is a cubic field.

The hard direction ("a root forces `p ≡ ±1`") and the hard existence direction
("`p ≡ −1` forces a root") are both proved by transporting the question into
the group `GL₂(𝔽_p)`: the companion matrix of `Y² − xY + 1` has order `7`
exactly when `x` is a root of `f`, and Cauchy's theorem supplies an order-`7`
matrix in the converse direction, whose trace is then forced to be a root of
`f` by a Cayley–Hamilton recursion.
-/

open Matrix Polynomial

namespace CyclicCubic

/-! ## The defining cubic -/

/-- `f(x) = x³ + x² − 2x − 1`, the minimal polynomial of `ζ₇ + ζ₇⁻¹`. -/
def fval {R : Type*} [CommRing R] (x : R) : R := x ^ 3 + x ^ 2 - 2 * x - 1

/-- The same cubic as a polynomial. -/
noncomputable def fpoly (R : Type*) [CommRing R] : R[X] := X ^ 3 + X ^ 2 - 2 * X - 1




/-! ## The `y + y⁻¹` substitution -/



/-! ## Small decidable facts about `ZMod 7` -/






/-! ## `2 × 2` matrix toolkit -/

section Matrices

variable {R : Type*} [CommRing R]






end Matrices

/-! ## The splitting criterion -/

section Prime

variable (p : ℕ) [hp : Fact p.Prime]






end Prime

/-! ## One root forces three: only two types -/

section Roots

variable {R : Type*} [CommRing R] [IsDomain R]





end Roots

/-! ## Irreducibility: the inert type -/

section Irred

variable (p : ℕ) [hp : Fact p.Prime]



/-- The **residue degree** of an unramified prime in the cyclic cubic field:
`1` when `p ≡ ±1 (mod 7)` (three primes above `p`), `3` otherwise (inert). -/
def resDeg (r : ZMod 7) : ℕ := if r = 1 ∨ r = 6 then 1 else 3





end Irred

/-! ## The base field: `f` is the minimal polynomial of `ζ₇ + ζ₇⁻¹` -/

section Rational






end Rational

end CyclicCubic


