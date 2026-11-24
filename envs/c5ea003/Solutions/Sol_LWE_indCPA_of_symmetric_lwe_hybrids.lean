-- Prove2me | solution 1 for LWE.indCPA_of_symmetric_lwe_hybrids
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:56:36.327739+00:00
-- url     : https://prove2.me/submissions/f8ea78d3-bada-4df2-8b52-ec7c468a88df

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

theorem l1Gap_symm_aux {Ω : Type*} [Fintype Ω] (P Q : FinitePMF Ω) :
    l1Gap P Q = l1Gap Q P := by
  simp [l1Gap, abs_sub_comm]

theorem l1Gap_triangle_aux {Ω : Type*} [Fintype Ω] (P Q R : FinitePMF Ω) :
    l1Gap P R ≤ l1Gap P Q + l1Gap Q R := by
  simp only [l1Gap]
  rw [← sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => abs_sub_le _ _ _

theorem hybrid_l1Gap_aux {Ω : Type*} [Fintype Ω] (G : ℕ → FinitePMF Ω) :
    ∀ k : ℕ, l1Gap (G 0) (G k) ≤ ∑ i ∈ range k, l1Gap (G i) (G (i + 1)) := by
  intro k
  induction k with
  | zero =>
    simp [l1Gap]
  | succ k ih =>
    calc l1Gap (G 0) (G (k + 1))
        ≤ l1Gap (G 0) (G k) + l1Gap (G k) (G (k + 1)) := l1Gap_triangle_aux _ _ _
      _ ≤ ∑ i ∈ range k, l1Gap (G i) (G (i + 1)) + l1Gap (G k) (G (k + 1)) := by exact add_le_add_left ih _
      _ = ∑ i ∈ range (k + 1), l1Gap (G i) (G (i + 1)) := by simp [Finset.sum_range_succ]

theorem solution {Ω : Type*} [Fintype Ω]
    (E : EncryptionExperiment Ω) (ideal : FinitePMF Ω)
    (G₀ G₁ : ℕ → FinitePMF Ω) (k : ℕ) (ε : ℝ)
    (h₀start : G₀ 0 = E.challenge false) (h₀end : G₀ k = ideal)
    (h₁start : G₁ 0 = E.challenge true) (h₁end : G₁ k = ideal)
    (h₀hop : ∀ i < k, l1Gap (G₀ i) (G₀ (i + 1)) ≤ ε)
    (h₁hop : ∀ i < k, l1Gap (G₁ i) (G₁ (i + 1)) ≤ ε) :
    indCPAGap E ≤ 2 * (k * ε) := by
  have hbound₀ : l1Gap (G₀ 0) ideal ≤ k * ε := by
    have step1 : l1Gap (G₀ 0) ideal = l1Gap (G₀ 0) (G₀ k) := by rw [h₀end]
    rw [step1]
    exact le_trans (hybrid_l1Gap_aux G₀ k)
      (by simpa [Finset.card_range] using Finset.sum_le_card_nsmul (Finset.range k) _ _ fun i hi => h₀hop i (Finset.mem_range.mp hi))
  have hbound₁ : l1Gap (G₁ 0) ideal ≤ k * ε := by
    have step1 : l1Gap (G₁ 0) ideal = l1Gap (G₁ 0) (G₁ k) := by rw [h₁end]
    rw [step1]
    exact le_trans (hybrid_l1Gap_aux G₁ k)
      (by simpa [Finset.card_range] using Finset.sum_le_card_nsmul (Finset.range k) _ _ fun i hi => h₁hop i (Finset.mem_range.mp hi))
  calc indCPAGap E = l1Gap (E.challenge false) (E.challenge true) := rfl
    _ = l1Gap (G₀ 0) (G₁ 0) := by rw [h₀start, h₁start]
    _ ≤ l1Gap (G₀ 0) ideal + l1Gap (G₁ 0) ideal := by
        have := l1Gap_triangle_aux (G₀ 0) ideal (G₁ 0); simpa [l1Gap_symm_aux ideal (G₁ 0)] using this
    _ ≤ k * ε + k * ε := add_le_add hbound₀ hbound₁
    _ = 2 * (k * ε) := by ring

#print axioms solution
