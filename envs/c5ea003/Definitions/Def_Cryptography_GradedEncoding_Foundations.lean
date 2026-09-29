-- Prove2me | Definitions.Def_Cryptography_GradedEncoding_Foundations
-- name    : Cryptography_GradedEncoding_Foundations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:55.348576+00:00
-- url     : https://prove2.me/theorems/a891c842-5f9e-4d37-ab2d-499cc5d5d082
-- title:
--   Aether Catalog definitions — Cryptography_GradedEncoding_Foundations
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.GradedEncoding.Foundations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/GradedEncoding/Foundations.lean by skeleton subtraction
import Mathlib

/-!
# Algebraic foundations for graded encoding systems

This file isolates the algebraic interface needed by multilinear Diffie--Hellman
reductions. It builds on Mathlib's `CommMonoid`; no new group operation is
introduced. Levels are tracked by the type of each encoding.
-/

open scoped BigOperators

namespace Cryptography.GradedEncoding

universe u v

/-- A graded encoding system over an existing commutative monoid. Multiplication
adds levels and agrees with multiplication of plaintexts on canonical encodings. -/
structure System (R : Type u) [CommMonoid R] where
  Code : ℕ → Type v
  encode : (level : ℕ) → R → Code level
  mul : {i j : ℕ} → Code i → Code j → Code (i + j)
  mul_encode : ∀ {i j : ℕ} (x y : R),
    mul (encode i x) (encode j y) = encode (i + j) (x * y)

namespace System

variable {R : Type u} [CommMonoid R]

/-- Canonical multilinear evaluation of plaintext inputs. The result level is
exactly the number of inputs. -/
def multilinearEval (S : System R) (xs : List R) : S.Code xs.length :=
  S.encode xs.length xs.prod


/-- A canonical `k`-multilinear Diffie--Hellman source challenge. -/
structure MDHSource (R : Type u) (k : ℕ) where
  exponents : Fin k → R

/-- The multilinear Diffie--Hellman target in the plaintext monoid. -/
def MDHSource.target {k : ℕ} (C : MDHSource R k) : R :=
  ∏ i, C.exponents i

/-- The public graded transcript associated with a source challenge. -/
structure MDHTranscript (S : System R) (k : ℕ) where
  publicEncoding : Fin k → S.Code 1
  targetEncoding : S.Code k

/-- Canonically encode a multilinear Diffie--Hellman source challenge. -/
def encodeChallenge (S : System R) {k : ℕ} (C : MDHSource R k) : MDHTranscript S k where
  publicEncoding := fun i => S.encode 1 (C.exponents i)
  targetEncoding := S.encode k C.target


end System
end Cryptography.GradedEncoding


