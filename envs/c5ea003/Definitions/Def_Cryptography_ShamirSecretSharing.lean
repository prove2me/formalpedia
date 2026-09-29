-- Prove2me | Definitions.Def_Cryptography_ShamirSecretSharing
-- name    : Cryptography_ShamirSecretSharing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:21.800247+00:00
-- url     : https://prove2.me/theorems/555ca9d7-8442-4780-b285-70301440e4fc
-- title:
--   Aether Catalog definitions — Cryptography_ShamirSecretSharing
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ShamirSecretSharing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ShamirSecretSharing.lean by skeleton subtraction
import Mathlib

/-!
# Shamir secret sharing

This file formalizes the algebraic and information-theoretic core of Shamir's
scheme over an arbitrary field.  A sharing polynomial has its secret as its
value at zero.  Privacy is expressed without choosing a probability API: after
fixing any values at `t - 1` nonzero locations, every possible secret has
exactly one degree-`< t` polynomial extension.  Consequently a uniformly
random sharing polynomial induces exactly the same observation distribution
for every secret.
-/

namespace ShamirSecretSharing

open Polynomial

variable {F : Type*} [Field F]

/-- The share carried by location `x` is polynomial evaluation at `x`. -/
def share (p : F[X]) (x : F) : F := p.eval x

/-- A polynomial is valid for threshold `t` and secret `secret` when its degree
is below `t` and its constant evaluation is the secret. -/
def ValidPolynomial (t : ℕ) (secret : F) (p : F[X]) : Prop :=
  p.degree < (t : WithBot ℕ) ∧ p.eval 0 = secret






end ShamirSecretSharing


