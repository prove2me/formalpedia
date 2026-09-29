-- Prove2me | Theorems.Thm_LWEOperational_expectation_sub_le_l1Gap
-- name    : LWEOperational.expectation_sub_le_l1Gap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:17:14.601568+00:00
-- url     : https://prove2.me/theorems/23bed7ee-00c4-49ae-86e4-00144e49cff3
-- title:
--   Operational meaning of the LWE hybrid distance.
-- statement:
--   **Operational meaning of the LWE hybrid distance.** Every test taking values
--   in `[0,1]` has distinguishing advantage at most the `ℓ¹` gap.
--
--   ```lean
--   theorem LWEOperational.expectation_sub_le_l1Gap{Ω : Type*} [Fintype Ω]
--       (P Q : FinitePMF Ω) (test : Ω → ℝ)
--       (htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1) :
--       |expectation P test - expectation Q test| ≤ l1Gap P Q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LWE/OperationalSecurity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LWE/OperationalSecurity.lean#L52

-- Thm stub generated from Cryptography/LWE/OperationalSecurity.lean
import Mathlib
import Definitions.Def_Cryptography_LWE_OperationalSecurity

/-!
# Operational Statistical Security for LWE Hybrids

This file turns the `ℓ¹` game distance used by the finite LWE IND-CPA
formalization into an operational statement about every bounded distinguisher.
It also isolates the ring-theoretic uniformity fact used in ring-LWE hybrids:
multiplication by a unit, followed by addition of an error, permutes the ring.
-/

open Finset BigOperators

noncomputable section

open LWEOperational

theorem LWEOperational.expectation_sub_le_l1Gap{Ω : Type*} [Fintype Ω]
    (P Q : FinitePMF Ω) (test : Ω → ℝ)
    (htest : ∀ x, 0 ≤ test x ∧ test x ≤ 1) :
    |expectation P test - expectation Q test| ≤ l1Gap P Q := by sorry
