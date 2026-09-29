-- Prove2me | Theorems.Thm_ShamirSecretSharing_degree_many_shares_do_not_reconstruct
-- name    : ShamirSecretSharing.degree_many_shares_do_not_reconstruct
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:00:38.314857+00:00
-- url     : https://prove2.me/theorems/fc78e6ee-e1b3-41fd-887b-17dcd4892cec
-- title:
--   With only `d` nonzero locations, uniqueness can fail for degree-`d`
-- statement:
--   With only `d` nonzero locations, uniqueness can fail for degree-`d`
--   polynomials: zero and the vanishing product agree at every supplied location
--   but encode different values at zero.
--
--   ```lean
--   theorem ShamirSecretSharing.degree_many_shares_do_not_reconstruct[DecidableEq F]
--       (locations : Finset F) (d : ℕ) (hcard : locations.card = d)
--       (hzero : 0 ∉ locations) :
--       ∃ p q : F[X], p ≠ q ∧
--         p.degree ≤ (d : WithBot ℕ) ∧ q.degree ≤ (d : WithBot ℕ) ∧
--         (∀ x ∈ locations, p.eval x = q.eval x) ∧ p.eval 0 ≠ q.eval 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ShamirSecretSharing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ShamirSecretSharing.lean#L141

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

theorem ShamirSecretSharing.degree_many_shares_do_not_reconstruct[DecidableEq F]
    (locations : Finset F) (d : ℕ) (hcard : locations.card = d)
    (hzero : 0 ∉ locations) :
    ∃ p q : F[X], p ≠ q ∧
      p.degree ≤ (d : WithBot ℕ) ∧ q.degree ≤ (d : WithBot ℕ) ∧
      (∀ x ∈ locations, p.eval x = q.eval x) ∧ p.eval 0 ≠ q.eval 0 := by sorry
