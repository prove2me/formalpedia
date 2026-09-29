-- Prove2me | Theorems.Thm_AlgebraicCodingTheory_reedSolomon_weight_bound
-- name    : AlgebraicCodingTheory.reedSolomon_weight_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:31:50.52026+00:00
-- url     : https://prove2.me/theorems/a4b15a91-e79c-44e3-bc7e-1e3a8a50d8d2
-- title:
--   A nonzero polynomial of degree less than `k`, evaluated at `n` distinct points,
-- statement:
--   A nonzero polynomial of degree less than `k`, evaluated at `n` distinct points,
--   has Hamming weight at least `n-k+1`.  This is the Reed–Solomon designed-distance
--   bound.
--
--   ```lean
--   theorem AlgebraicCodingTheory.reedSolomon_weight_bound{n k : ℕ} (points : Fin n → F)
--       (hpoints : Function.Injective points) (p : F[X]) (hp : p ≠ 0)
--       (hdeg : p.natDegree < k) (hkn : k ≤ n) :
--       n - k + 1 ≤ (Finset.univ.filter fun i => reedSolomonEval points p i ≠ 0).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AlgebraicCodingTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AlgebraicCodingTheory.lean#L51

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

theorem AlgebraicCodingTheory.reedSolomon_weight_bound{n k : ℕ} (points : Fin n → F)
    (hpoints : Function.Injective points) (p : F[X]) (hp : p ≠ 0)
    (hdeg : p.natDegree < k) (hkn : k ≤ n) :
    n - k + 1 ≤ (Finset.univ.filter fun i => reedSolomonEval points p i ≠ 0).card := by sorry
