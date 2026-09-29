-- Prove2me | Theorems.Thm_seti_orthogonality_decomposition
-- name    : seti_orthogonality_decomposition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:57:49.083462+00:00
-- url     : https://prove2.me/theorems/2f4c1bbd-8ad9-4777-87d6-e365adc0736a
-- title:
--   Seti orthogonality decomposition
-- statement:
--   Formal statement of `seti_orthogonality_decomposition` from the Aether Catalog (Speculative). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem seti_orthogonality_decomposition    {q : ℕ} [NeZero q] [Fintype (ZMod q)ˣ]
--       (χ ψ : DirichletCharacter ℂ q) (h : χ ≠ ψ) :
--       ∑ a : (ZMod q)ˣ, χ a * ψ (a⁻¹) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/SciFi/SETIOrthogonality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/SciFi/SETIOrthogonality.lean#L23

-- Thm stub generated from Speculative/SciFi/SETIOrthogonality.lean
import Mathlib

/-! # CatalogBuild.Speculative.SciFi.SETIOrthogonality

Auto-generated from theorem catalog database.
Domain: Speculative/SciFi
Declarations: 1
Research Arc: Cryptographic Gravity
Novelty: 0.95
-/

/-
SETI Prime-Modulated Orthogonality Decomposition.

The SETI array detects weak periodic signals buried in cosmic noise. A linguist-druid from the EML project proposes that advanced civilizations broadcast on carriers whose periods are prime powers, modulating each channel by a distinct Dirichlet character. Because non-principal characters are orthogonal under pointwise multiplication, a receiver that integrates over one complete period can separate an arbitrarily large number of alien conversations with zero cross-talk. The theorem guarantees that even if the Milky Way is a noisy party, every speaker can be isolated by number-theoretic tuning.

Mathematical Concept: Fourier analysis on finite abelian groups (orthogonality relations for Dirichlet characters). Alien carriers encoded with distinct prime-periodic modulations behave as orthogonal basis vectors in the Hilbert space of functions on (ℤ/qℤ)×. Cross-correlation over a complete period vanishes exactly, enabling noiseless channel separation.

Proof Strategy: Use the group-ring structure of ℂ[(ℤ/qℤ)×]. Recognize the sum as the inner product ⟨χ, ψ⟩ in the space of class functions. Apply the Orthogonality Relations for irreducible characters of finite abelian groups: the sum over the group of χ(a)ψ(a)⁻¹ equals |G| if χ = ψ and 0 otherwise. In Lean, unfold the definition of DirichletCharacter, use the fact that distinct characters have distinct kernels, and apply the orthogonality lemma from the representation theory of finite groups (available in mathlib via AddChar/Pontryagin duality).

Difficulty: master
Arc: Cryptographic Gravity
-/

theorem seti_orthogonality_decomposition    {q : ℕ} [NeZero q] [Fintype (ZMod q)ˣ]
    (χ ψ : DirichletCharacter ℂ q) (h : χ ≠ ψ) :
    ∑ a : (ZMod q)ˣ, χ a * ψ (a⁻¹) = 0 := by sorry
