-- Prove2me | Theorems.Thm_AlgebraicCodingTheory_reedSolomon_distance_bound
-- name    : AlgebraicCodingTheory.reedSolomon_distance_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:31:40.291852+00:00
-- url     : https://prove2.me/theorems/c2b1a944-cc4f-4890-a628-2f6727a142a2
-- title:
--   Distinct messages of degree less than `k` produce words separated by at least
-- statement:
--   Distinct messages of degree less than `k` produce words separated by at least
--   `n-k+1` positions.
--
--   ```lean
--   theorem AlgebraicCodingTheory.reedSolomon_distance_bound{n k : ℕ} (points : Fin n → F)
--       (hpoints : Function.Injective points) (p q : F[X]) (hpq : p ≠ q)
--       (hpdeg : p.natDegree < k) (hqdeg : q.natDegree < k) (hkn : k ≤ n) :
--       n - k + 1 ≤ hammingDistance (reedSolomonEval points p) (reedSolomonEval points q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AlgebraicCodingTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AlgebraicCodingTheory.lean#L82

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

theorem AlgebraicCodingTheory.reedSolomon_distance_bound{n k : ℕ} (points : Fin n → F)
    (hpoints : Function.Injective points) (p q : F[X]) (hpq : p ≠ q)
    (hpdeg : p.natDegree < k) (hqdeg : q.natDegree < k) (hkn : k ≤ n) :
    n - k + 1 ≤ hammingDistance (reedSolomonEval points p) (reedSolomonEval points q) := by sorry
