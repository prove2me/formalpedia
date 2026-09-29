-- Prove2me | Theorems.Thm_LWE_indCPA_of_symmetric_lwe_hybrids
-- name    : LWE.indCPA_of_symmetric_lwe_hybrids
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:56:12.293585+00:00
-- url     : https://prove2.me/theorems/73a277a2-8e50-4e39-bc05-f26be0c56eab
-- title:
--   Combining a `k`-hop LWE replacement on each challenge branch gives a
-- statement:
--   Combining a `k`-hop LWE replacement on each challenge branch gives a
--   `2kε` IND-CPA bound.
--
--   ```lean
--   theorem LWE.indCPA_of_symmetric_lwe_hybrids{Ω : Type*} [Fintype Ω]
--       (E : EncryptionExperiment Ω) (ideal : FinitePMF Ω)
--       (G₀ G₁ : ℕ → FinitePMF Ω) (k : ℕ) (ε : ℝ)
--       (h₀start : G₀ 0 = E.challenge false) (h₀end : G₀ k = ideal)
--       (h₁start : G₁ 0 = E.challenge true) (h₁end : G₁ k = ideal)
--       (h₀hop : ∀ i < k, l1Gap (G₀ i) (G₀ (i + 1)) ≤ ε)
--       (h₁hop : ∀ i < k, l1Gap (G₁ i) (G₁ (i + 1)) ≤ ε) :
--       indCPAGap E ≤ 2 * (k * ε) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LWE/INDCPA.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LWE/INDCPA.lean#L98

-- Thm stub generated from Cryptography/LWE/INDCPA.lean
import Mathlib
import Definitions.Def_Cryptography_LWE_INDCPA

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

open LWE

theorem LWE.indCPA_of_symmetric_lwe_hybrids{Ω : Type*} [Fintype Ω]
    (E : EncryptionExperiment Ω) (ideal : FinitePMF Ω)
    (G₀ G₁ : ℕ → FinitePMF Ω) (k : ℕ) (ε : ℝ)
    (h₀start : G₀ 0 = E.challenge false) (h₀end : G₀ k = ideal)
    (h₁start : G₁ 0 = E.challenge true) (h₁end : G₁ k = ideal)
    (h₀hop : ∀ i < k, l1Gap (G₀ i) (G₀ (i + 1)) ≤ ε)
    (h₁hop : ∀ i < k, l1Gap (G₁ i) (G₁ (i + 1)) ≤ ε) :
    indCPAGap E ≤ 2 * (k * ε) := by sorry
