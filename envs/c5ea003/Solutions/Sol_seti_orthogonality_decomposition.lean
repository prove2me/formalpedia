-- Prove2me | solution 1 for seti_orthogonality_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:26:21.993666+00:00
-- url     : https://prove2.me/submissions/b85d1ca3-73ec-46c5-9258-3c675832bde8

-- Sol generated from Speculative/SciFi/SETIOrthogonality.lean
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

theorem solution    {q : ℕ} [NeZero q] [Fintype (ZMod q)ˣ]
    (χ ψ : DirichletCharacter ℂ q) (h : χ ≠ ψ) :
    ∑ a : (ZMod q)ˣ, χ a * ψ (a⁻¹) = 0 := by
  -- Recognize that the sum can be rewritten using the properties of characters.
  have h_rewrite : ∑ a : (ZMod q)ˣ, χ a * ψ (a⁻¹) = ∑ a : (ZMod q)ˣ, (χ * ψ⁻¹) a := by
    simp +decide [MulChar.mul_apply, MulChar.inv_apply];
  -- Since $\chi \neq \psi$, we have $\chi * \psi⁻¹ \neq 1$.
  have h_ne_one : χ * ψ⁻¹ ≠ 1 := by
    exact fun h' => h <| by simpa using eq_inv_of_mul_eq_one_left h';
  convert MulChar.sum_eq_zero_of_ne_one h_ne_one;
  rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : ( ZMod q ) ˣ => ( x : ZMod q ) ) Finset.univ ) ) ];
  · rw [ Finset.sum_image ] ; aesop;
    exact fun x _ y _ hxy => Units.ext hxy;
  · simp +contextual [ DirichletCharacter ];
    intro x hx; haveI := Fact.mk ( NeZero.pos q ) ; exact Or.inl ( χ.map_nonunit <| by contrapose! hx; aesop ) ;
