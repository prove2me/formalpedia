-- Prove2me | Theorems.Thm_CyclicCubic_residue_of_root
-- name    : CyclicCubic.residue_of_root
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:35:04.196156+00:00
-- url     : https://prove2.me/theorems/60dcbd53-5a4b-4703-9b06-57b4d20615de
-- title:
--   Hard direction.
-- statement:
--   **Hard direction.**  A root of `f` in `𝔽_p` forces `p ≡ ±1 (mod 7)`.
--
--   ```lean
--   theorem CyclicCubic.residue_of_root(hp7 : p ≠ 7) (h : ∃ x : ZMod p, fval x = 0) :
--       (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/CyclicCubicTypeChannel/Splitting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/CyclicCubicTypeChannel/Splitting.lean#L156

-- Thm stub generated from Applications/CyclicCubicTypeChannel/Splitting.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
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

open CyclicCubic

/-! ## The defining cubic -/






/-! ## The `y + y⁻¹` substitution -/



/-! ## Small decidable facts about `ZMod 7` -/






/-! ## `2 × 2` matrix toolkit -/


variable {R : Type*} [CommRing R]







/-! ## The splitting criterion -/


variable (p : ℕ) [hp : Fact p.Prime]

theorem CyclicCubic.residue_of_root(hp7 : p ≠ 7) (h : ∃ x : ZMod p, fval x = 0) :
    (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6 := by sorry
