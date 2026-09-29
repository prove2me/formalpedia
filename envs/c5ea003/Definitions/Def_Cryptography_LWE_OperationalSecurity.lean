-- Prove2me | Definitions.Def_Cryptography_LWE_OperationalSecurity
-- name    : Cryptography_LWE_OperationalSecurity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:39:22.717033+00:00
-- url     : https://prove2.me/theorems/a3a18910-4409-4087-ae7c-45a1e52f0074
-- title:
--   Aether Catalog definitions — Cryptography_LWE_OperationalSecurity
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LWE.OperationalSecurity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LWE/OperationalSecurity.lean by skeleton subtraction
import Mathlib

/-!
# Operational Statistical Security for LWE Hybrids

This file turns the `ℓ¹` game distance used by the finite LWE IND-CPA
formalization into an operational statement about every bounded distinguisher.
It also isolates the ring-theoretic uniformity fact used in ring-LWE hybrids:
multiplication by a unit, followed by addition of an error, permutes the ring.
-/

open Finset BigOperators

noncomputable section

namespace LWEOperational

/-- A probability mass function on a finite transcript space. -/
structure FinitePMF (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

/-- The `ℓ¹` gap between two finite experiments. -/
def l1Gap {Ω : Type*} [Fintype Ω] (P Q : FinitePMF Ω) : ℝ :=
  ∑ x, |P.mass x - Q.mass x|

/-- The two challenge ensembles of an encryption experiment. -/
structure EncryptionExperiment (Ω : Type*) [Fintype Ω] where
  challenge : Bool → FinitePMF Ω


/-- The expectation of a real-valued test in a finite experiment. -/
def expectation {Ω : Type*} [Fintype Ω] (P : FinitePMF Ω) (test : Ω → ℝ) : ℝ :=
  ∑ x, P.mass x * test x




end LWEOperational

namespace RingLWE

variable {R : Type*} [CommRing R]




end RingLWE

end


