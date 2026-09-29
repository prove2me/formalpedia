-- Prove2me | Theorems.Thm_bounded_box_sis_witness
-- name    : bounded_box_sis_witness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:09:23.018924+00:00
-- url     : https://prove2.me/theorems/6e3e8d07-bd88-4601-9e02-7d8a12626a5d
-- title:
--   Short-vector pigeonhole (SIS witness).
-- statement:
--   **Short-vector pigeonhole (SIS witness).**  If the box `{0, …, 2B}ⁿ` has
--   more points than the syndrome space `(ℤ/q)ᵐ`, then there is a nonzero integer
--   vector `z` with `|zᵢ| ≤ 2B` whose image under `A` vanishes modulo `q`.
--
--   ```lean
--   theorem bounded_box_sis_witness{m n q B : ℕ} (hq : 0 < q)
--       (A : Matrix (Fin m) (Fin n) ℤ)
--       (hsize : q ^ m < (2 * B + 1) ^ n) :
--       ∃ z : Fin n → ℤ,
--         z ≠ 0 ∧
--         (∀ i, |z i| ≤ 2 * (B : ℤ)) ∧
--         (∀ j : Fin m, (∑ i, A j i * z i : ℤ) ≡ 0 [ZMOD q]) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/GeometricCryptanalysis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/GeometricCryptanalysis.lean#L43

-- Thm stub generated from Cryptography/GeometricCryptanalysis.lean
import Mathlib
import Definitions.Def_Cryptography_GeometricCryptanalysis
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A geometric pigeonhole for short modular kernel vectors

This file supplies the short-vector existence statement used by
`Cryptography.ParkingFunctionPolytopes.Core`: a counting (pigeonhole) argument
of Minkowski type showing that a box which is larger than the syndrome space of
a modular linear map contains a nonzero short vector in the kernel of that map.

If the integer box `{0, …, 2B}ⁿ` has more points than the syndrome space
`(ℤ/q)ᵐ`, two distinct box points have the same syndrome under `A`, and their
difference is a nonzero vector `z` with `|zᵢ| ≤ 2B` and `A z ≡ 0 (mod q)`.

This is the elementary combinatorial core of the Short Integer Solution (SIS)
problem: hardness assumptions aside, *existence* of a short kernel vector is
pure counting.
-/

open Finset

theorem bounded_box_sis_witness{m n q B : ℕ} (hq : 0 < q)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hsize : q ^ m < (2 * B + 1) ^ n) :
    ∃ z : Fin n → ℤ,
      z ≠ 0 ∧
      (∀ i, |z i| ≤ 2 * (B : ℤ)) ∧
      (∀ j : Fin m, (∑ i, A j i * z i : ℤ) ≡ 0 [ZMOD q]) := by sorry
