-- Prove2me | Definitions.Def_Bridges_LanglandsSymmetricSquareFunctoriality
-- name    : Bridges_LanglandsSymmetricSquareFunctoriality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:27:10.395265+00:00
-- url     : https://prove2.me/theorems/f5123466-2757-4670-951e-187328454413
-- title:
--   Aether Catalog definitions — Bridges_LanglandsSymmetricSquareFunctoriality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LanglandsSymmetricSquareFunctoriality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LanglandsSymmetricSquareFunctoriality.lean by skeleton subtraction
import Mathlib

/-!
# The unramified symmetric-square transfer from GL(2) to GL(3)

This file gives a self-contained local formalization of the Satake-parameter part of
Langlands functoriality.  An unramified representation is represented by its finite
family of Satake parameters.  Its standard local L-factor is encoded by the Euler
denominator

`∏ᵢ (1 - αᵢ X)`.

For parameters `(a,b)` on GL(2), the symmetric-square transfer has parameters
`(a², ab, b²)` on GL(3).  The results below prove compatibility with scalar extension,
central characters, standard local L-factors, and the decomposition of the tensor-square
Euler denominator into symmetric-square and determinant factors.
-/

namespace LanglandsFunctoriality

open scoped BigOperators
open Polynomial

/-- Unramified automorphic data of rank `n`, represented by its Satake parameters. -/
@[ext] structure UnramifiedAutomorphicRepresentation (R : Type*) (n : ℕ) where
  satake : Fin n → R

namespace UnramifiedAutomorphicRepresentation

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- Scalar extension of unramified Satake data. -/
def map (f : R →+* S) (π : UnramifiedAutomorphicRepresentation R n) :
    UnramifiedAutomorphicRepresentation S n :=
  ⟨fun i => f (π.satake i)⟩

/-- The Euler denominator of the standard unramified local L-factor. -/
noncomputable def eulerDenominator (π : UnramifiedAutomorphicRepresentation R n) : Polynomial R :=
  ∏ i : Fin n, (1 - C (π.satake i) * X)

/-- The product of Satake parameters, corresponding to the unramified central character. -/
def centralCharacter (π : UnramifiedAutomorphicRepresentation R n) : R :=
  ∏ i : Fin n, π.satake i

/-- The GL(2) unramified datum with Satake parameters `(a,b)`. -/
def gl2 (a b : R) : UnramifiedAutomorphicRepresentation R 2 :=
  ⟨![a, b]⟩

/-- The symmetric-square transfer from GL(2) to GL(3), on Satake parameters. -/
def symmetricSquare (π : UnramifiedAutomorphicRepresentation R 2) :
    UnramifiedAutomorphicRepresentation R 3 :=
  ⟨![π.satake 0 ^ 2, π.satake 0 * π.satake 1, π.satake 1 ^ 2]⟩

/-- The determinant character attached to GL(2) Satake data. -/
def determinantCharacter (π : UnramifiedAutomorphicRepresentation R 2) :
    UnramifiedAutomorphicRepresentation R 1 :=
  ⟨![π.satake 0 * π.satake 1]⟩

/-- The tensor-square parameter list, with multiplicity, for a GL(2) datum. -/
def tensorSquare (π : UnramifiedAutomorphicRepresentation R 2) :
    UnramifiedAutomorphicRepresentation R 4 :=
  ⟨![π.satake 0 ^ 2, π.satake 0 * π.satake 1,
      π.satake 0 * π.satake 1, π.satake 1 ^ 2]⟩









end UnramifiedAutomorphicRepresentation
end LanglandsFunctoriality


