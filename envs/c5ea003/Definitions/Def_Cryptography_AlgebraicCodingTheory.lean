-- Prove2me | Definitions.Def_Cryptography_AlgebraicCodingTheory
-- name    : Cryptography_AlgebraicCodingTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:02:46.836591+00:00
-- url     : https://prove2.me/theorems/34a441eb-7729-4265-9878-5f96f11600da
-- title:
--   Aether Catalog definitions — Cryptography_AlgebraicCodingTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.AlgebraicCodingTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/AlgebraicCodingTheory.lean by skeleton subtraction
import Mathlib

/-!
# Reed–Solomon codes over finite fields

This file gives a direct polynomial-evaluation construction of Reed–Solomon codes and
proves their designed-distance bound.  It also derives injectivity, separation, and a
unique-decoding theorem from the bound.
-/

namespace AlgebraicCodingTheory

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- Evaluation of a polynomial at a finite family of code locations. -/
def reedSolomonEval {n : ℕ} (points : Fin n → F) (p : F[X]) : Fin n → F :=
  fun i => p.eval (points i)

/-- Hamming distance on words of fixed length. -/
def hammingDistance {n : ℕ} {α : Type*} [DecidableEq α] (u v : Fin n → α) : ℕ :=
  (Finset.univ.filter fun i => u i ≠ v i).card







end AlgebraicCodingTheory


