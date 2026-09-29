-- Prove2me | Theorems.Thm_ShamirSecretSharing_reconstruct_from_degree_plus_one
-- name    : ShamirSecretSharing.reconstruct_from_degree_plus_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:00:42.206792+00:00
-- url     : https://prove2.me/theorems/592b5281-0fc4-4330-a1c2-2a9582048425
-- title:
--   Values at `d+1` distinct locations uniquely determine a polynomial of degree
-- statement:
--   Values at `d+1` distinct locations uniquely determine a polynomial of degree
--   at most `d`.  This is reconstruction at the Shamir threshold.
--
--   ```lean
--   theorem ShamirSecretSharing.reconstruct_from_degree_plus_one[DecidableEq F]
--       (locations : Finset F) (d : ℕ) (hcard : locations.card = d + 1)
--       (p q : F[X]) (hp : p.degree ≤ (d : WithBot ℕ))
--       (hq : q.degree ≤ (d : WithBot ℕ))
--       (hagrees : ∀ x ∈ locations, p.eval x = q.eval x) : p = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ShamirSecretSharing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ShamirSecretSharing.lean#L116

-- Thm stub generated from Cryptography/ShamirSecretSharing.lean
import Mathlib
import Definitions.Def_Cryptography_ShamirSecretSharing

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

open ShamirSecretSharing

open Polynomial

variable {F : Type*} [Field F]

theorem ShamirSecretSharing.reconstruct_from_degree_plus_one[DecidableEq F]
    (locations : Finset F) (d : ℕ) (hcard : locations.card = d + 1)
    (p q : F[X]) (hp : p.degree ≤ (d : WithBot ℕ))
    (hq : q.degree ≤ (d : WithBot ℕ))
    (hagrees : ∀ x ∈ locations, p.eval x = q.eval x) : p = q := by sorry
