-- Prove2me | Theorems.Thm_ShamirSecretSharing_perfect_privacy_extension
-- name    : ShamirSecretSharing.perfect_privacy_extension
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:00:58.816774+00:00
-- url     : https://prove2.me/theorems/2e692a39-3915-46b4-9c29-78863a7b1396
-- title:
--   The unique low-degree extension of prescribed observations and a prescribed
-- statement:
--   The unique low-degree extension of prescribed observations and a prescribed
--   secret.  This is the exact-counting form of perfect privacy: any observation at
--   `t-1` nonzero locations is compatible with every secret in exactly one way.
--
--   ```lean
--   theorem ShamirSecretSharing.perfect_privacy_extension[DecidableEq F]
--       (observed : Finset F) (hzero : 0 ∉ observed) (t : ℕ)
--       (hcard : observed.card + 1 = t) (values : F → F) (secret : F) :
--       ∃! p : F[X],
--         p.degree < (t : WithBot ℕ) ∧ p.eval 0 = secret ∧
--           ∀ x ∈ observed, p.eval x = values x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ShamirSecretSharing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ShamirSecretSharing.lean#L28

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

theorem ShamirSecretSharing.perfect_privacy_extension[DecidableEq F]
    (observed : Finset F) (hzero : 0 ∉ observed) (t : ℕ)
    (hcard : observed.card + 1 = t) (values : F → F) (secret : F) :
    ∃! p : F[X],
      p.degree < (t : WithBot ℕ) ∧ p.eval 0 = secret ∧
        ∀ x ∈ observed, p.eval x = values x := by sorry
