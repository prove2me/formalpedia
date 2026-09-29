-- Prove2me | Definitions.Def_Cryptography_LWE_INDCPA
-- name    : Cryptography_LWE_INDCPA
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:39:44.59406+00:00
-- url     : https://prove2.me/theorems/4503d47b-30a6-4952-9c90-8b937e018df6
-- title:
--   Aether Catalog definitions — Cryptography_LWE_INDCPA
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LWE.INDCPA`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LWE/INDCPA.lean by skeleton subtraction
import Mathlib

/-!
# A Game-Hopping Security Theorem for LWE Encryption

This file formalizes the quantitative core of the IND-CPA proof for Regev-style
LWE encryption.  Ciphertext ensembles are represented by their probability mass
functions on a finite transcript space.  Their `ℓ¹` gap is twice statistical
distance.  The main theorem says that if encryption of either challenge bit can
be replaced by the same message-independent ideal ensemble with respective
losses `ε₀` and `ε₁`, then the IND-CPA gap is at most `ε₀ + ε₁`.

This isolates the exact final game hop used after an LWE assumption has replaced
public-key samples and ciphertext inner products by uniform values.  A second
result proves the general hybrid lemma and its linear-loss corollary.
-/

open Finset BigOperators

noncomputable section

namespace LWE

/-- A probability mass function on a finite transcript space. -/
structure FinitePMF (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

/-- The `ℓ¹` gap between finite ensembles (twice their statistical distance). -/
def l1Gap {Ω : Type*} [Fintype Ω] (P Q : FinitePMF Ω) : ℝ :=
  ∑ x, |P.mass x - Q.mass x|




/-- The two challenge ciphertext ensembles of an encryption experiment. -/
structure EncryptionExperiment (Ω : Type*) [Fintype Ω] where
  challenge : Bool → FinitePMF Ω

/-- IND-CPA distinguishing gap, in the `ℓ¹` normalization. -/
def indCPAGap {Ω : Type*} [Fintype Ω] (E : EncryptionExperiment Ω) : ℝ :=
  l1Gap (E.challenge false) (E.challenge true)





/-! ## Kernel-checked small-case evidence

For the deterministic distributions on `Bool`, the opposite point masses have
`ℓ¹` gap `2`, while identical point masses have gap `0`.  These examples check
the normalization and edge cases used by the general theorem.
-/


end LWE

end


