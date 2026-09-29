-- Prove2me | Definitions.Def_Cryptography_GeometricCryptanalysis
-- name    : Cryptography_GeometricCryptanalysis
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:36.108422+00:00
-- url     : https://prove2.me/theorems/4bde6715-c7ff-4b90-be81-41820e99b8a5
-- title:
--   Aether Catalog definitions — Cryptography_GeometricCryptanalysis
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.GeometricCryptanalysis`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/GeometricCryptanalysis.lean by skeleton subtraction
import Mathlib
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

/-- The syndrome of an integer vector under a modular linear map. -/
def sisSyndrome {m n q : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℤ) :
    Fin m → ZMod q :=
  fun j => ((∑ i, A j i * x i : ℤ) : ZMod q)


