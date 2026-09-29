-- Prove2me | Theorems.Thm_AlgebraicCodingTheory_card_zero_evaluations_le_natDegree
-- name    : AlgebraicCodingTheory.card_zero_evaluations_le_natDegree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:31:40.67186+00:00
-- url     : https://prove2.me/theorems/e6108ee3-d90c-464e-b69b-c6542d1497db
-- title:
--   The number of zero evaluations of a nonzero polynomial at distinct points is at
-- statement:
--   The number of zero evaluations of a nonzero polynomial at distinct points is at
--   most its degree.
--
--   ```lean
--   theorem AlgebraicCodingTheory.card_zero_evaluations_le_natDegree{n : ℕ} (points : Fin n → F)
--       (hpoints : Function.Injective points) (p : F[X]) (hp : p ≠ 0) :
--       (Finset.univ.filter fun i => p.eval (points i) = 0).card ≤ p.natDegree := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AlgebraicCodingTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AlgebraicCodingTheory.lean#L24

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

theorem AlgebraicCodingTheory.card_zero_evaluations_le_natDegree{n : ℕ} (points : Fin n → F)
    (hpoints : Function.Injective points) (p : F[X]) (hp : p ≠ 0) :
    (Finset.univ.filter fun i => p.eval (points i) = 0).card ≤ p.natDegree := by sorry
