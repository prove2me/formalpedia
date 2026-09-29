-- Prove2me | Theorems.Thm_LWEOperational_boolean_distinguisher_advantage
-- name    : LWEOperational.boolean_distinguisher_advantage
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:17:52.702226+00:00
-- url     : https://prove2.me/theorems/ce586606-5fb5-42e6-b9c9-526a8ce70ed1
-- title:
--   A deterministic Boolean adversary's acceptance-probability advantage is
-- statement:
--   A deterministic Boolean adversary's acceptance-probability advantage is
--   bounded by the `ℓ¹` gap between its two input ensembles.
--
--   ```lean
--   theorem LWEOperational.boolean_distinguisher_advantage{Ω : Type*} [Fintype Ω]
--       (P Q : FinitePMF Ω) (adversary : Ω → Bool) :
--       |(∑ x with adversary x = true, P.mass x) -
--         (∑ x with adversary x = true, Q.mass x)| ≤ l1Gap P Q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LWE/OperationalSecurity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LWE/OperationalSecurity.lean#L75

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

theorem LWEOperational.boolean_distinguisher_advantage{Ω : Type*} [Fintype Ω]
    (P Q : FinitePMF Ω) (adversary : Ω → Bool) :
    |(∑ x with adversary x = true, P.mass x) -
      (∑ x with adversary x = true, Q.mass x)| ≤ l1Gap P Q := by sorry
