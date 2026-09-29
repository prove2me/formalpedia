-- Prove2me | Theorems.Thm_AlgebraicCodingTheory_unique_decode_of_separation
-- name    : AlgebraicCodingTheory.unique_decode_of_separation
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:01.267742+00:00
-- url     : https://prove2.me/theorems/05122494-68a4-459b-8716-cc1f55239575
-- title:
--   Metric form of unique decoding: two codewords at distance at least `d` cannot
-- statement:
--   Metric form of unique decoding: two codewords at distance at least `d` cannot
--   both lie within radius `t` of one received word when `2t < d`.
--
--   ```lean
--   theorem AlgebraicCodingTheory.unique_decode_of_separation{α : Type*} [DecidableEq α] {n d t : ℕ}
--       (x y received : Fin n → α) (hsep : d ≤ hammingDistance x y)
--       (hx : hammingDistance x received ≤ t)
--       (hy : hammingDistance y received ≤ t)
--       (hradius : 2 * t < d) : False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AlgebraicCodingTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AlgebraicCodingTheory.lean#L114

-- Thm stub generated from Cryptography/AlgebraicCodingTheory.lean
import Mathlib
import Definitions.Def_Cryptography_AlgebraicCodingTheory

/-!
# Reed–Solomon codes over finite fields

This file gives a direct polynomial-evaluation construction of Reed–Solomon codes and
proves their designed-distance bound.  It also derives injectivity, separation, and a
unique-decoding theorem from the bound.
-/

open AlgebraicCodingTheory

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

theorem AlgebraicCodingTheory.unique_decode_of_separation{α : Type*} [DecidableEq α] {n d t : ℕ}
    (x y received : Fin n → α) (hsep : d ≤ hammingDistance x y)
    (hx : hammingDistance x received ≤ t)
    (hy : hammingDistance y received ≤ t)
    (hradius : 2 * t < d) : False := by sorry
