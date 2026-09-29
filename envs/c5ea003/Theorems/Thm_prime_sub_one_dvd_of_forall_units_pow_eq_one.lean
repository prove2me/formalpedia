-- Prove2me | Theorems.Thm_prime_sub_one_dvd_of_forall_units_pow_eq_one
-- name    : prime_sub_one_dvd_of_forall_units_pow_eq_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:39.211637+00:00
-- url     : https://prove2.me/theorems/d67241a1-128f-4096-9cd6-aa9e6f3b191a
-- title:
--   Arithmetic bridge toward Korselt's criterion: if every unit of `ZMod n`
-- statement:
--   Arithmetic bridge toward Korselt's criterion: if every unit of `ZMod n`
--   satisfies `u ^ (n - 1) = 1`, then for every prime `p ∣ n` we have
--   `(p - 1) ∣ (n - 1)`.
--
--   The squarefreeness hypothesis `hsq` is part of the requested statement of
--   Korselt's criterion, but it turns out not to be needed for this arithmetic step,
--   so it is kept (unused) only to match the intended interface.
--
--   ```lean
--   theorem prime_sub_one_dvd_of_forall_units_pow_eq_one{n : ℕ} [NeZero n] (p : ℕ)
--       [Fact (Nat.Prime p)] (hp : p ∣ n) (hsq : Squarefree n)
--       (hunit : ∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1) : (p - 1) ∣ (n - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/KorseltUnitsBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/KorseltUnitsBridge.lean#L28

-- Thm stub generated from Bridges/PosetTheory/KorseltUnitsBridge.lean
import Mathlib

/-! # Korselt Units Bridge

An arithmetic bridge toward Korselt's criterion for Carmichael numbers.

If every unit of `ZMod n` satisfies `u ^ (n - 1) = 1`, then for every prime
`p ∣ n` we have `(p - 1) ∣ (n - 1)`.
-/

theorem prime_sub_one_dvd_of_forall_units_pow_eq_one{n : ℕ} [NeZero n] (p : ℕ)
    [Fact (Nat.Prime p)] (hp : p ∣ n) (hsq : Squarefree n)
    (hunit : ∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1) : (p - 1) ∣ (n - 1) := by sorry
