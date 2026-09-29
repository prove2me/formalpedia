-- Prove2me | solution 1 for mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T02:04:34.127879+00:00
-- url     : https://prove2.me/submissions/3d53d0b5-54e2-4ae1-8ca0-4ce33dac1a97

import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.DWZRestrictedValue Module
universe u
set_option autoImplicit false

theorem solution {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p q : IntegerZSplitProfile t) (k : ℕ) (hk : 0 < k)
    (hden : q.denominator = p.denominator * k)
    (hcount : ∀ a, q.count a = p.count a * k)
    (tau V : ℝ)
    (h : HasPrescribedZSixRestrictionValueAtLeast T bZ grade q tau V) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V := by
  -- Transport of the Z-allowed subtensor along an equality of word lengths.
  have transport : ∀ (n₁ n₂ : ℕ), n₁ = n₂ →
      ∀ (P₁ : MME.DWZComponentRestriction.PowIndex ι n₁ → Prop)
        (P₂ : MME.DWZComponentRestriction.PowIndex ι n₂ → Prop), HEq P₁ P₂ →
      ∀ (d₁ : DecidablePred P₁) (d₂ : DecidablePred P₂),
        @TensorObj.basisZAllowedSubtensor K _ (T.kronPow n₁)
            (MME.DWZComponentRestriction.PowIndex ι n₁)
            (MME.DWZComponentRestriction.kronPowModeBasis T 2 bZ n₁) P₁ d₁ =
          @TensorObj.basisZAllowedSubtensor K _ (T.kronPow n₂)
            (MME.DWZComponentRestriction.PowIndex ι n₂)
            (MME.DWZComponentRestriction.kronPowModeBasis T 2 bZ n₂) P₂ d₂ := by
    rintro n₁ n₂ rfl P₁ P₂ hP d₁ d₂
    obtain rfl : P₁ = P₂ := eq_of_heq hP
    obtain rfl : d₁ = d₂ := Subsingleton.elim d₁ d₂
    rfl
  -- The prescribed-word predicate depends only on the length and the target counts.
  have hword : ∀ (n₁ n₂ : ℕ), n₁ = n₂ → ∀ (c₁ c₂ : Fin t → ℕ), c₁ = c₂ →
      HEq (fun w : MME.DWZComponentRestriction.PowIndex ι n₁ ↦
              ∀ a : Fin t, leftGradeCount grade w a = c₁ a)
          (fun w : MME.DWZComponentRestriction.PowIndex ι n₂ ↦
              ∀ a : Fin t, leftGradeCount grade w a = c₂ a) := by
    rintro n₁ n₂ rfl c₁ c₂ rfl
    exact HEq.rfl
  have hlen : ∀ M : ℕ, p.length (k * M) = q.length M := by
    intro M
    show p.denominator * (k * M) = q.denominator * M
    rw [hden]
    exact (Nat.mul_assoc _ _ _).symm
  have hcnt : ∀ M : ℕ,
      (fun a : Fin t ↦ p.count a * (k * M)) = fun a : Fin t ↦ q.count a * M := by
    intro M
    funext a
    rw [hcount a]
    exact (Nat.mul_assoc _ _ _).symm
  have hpow : ∀ M : ℕ,
      prescribedZPower T bZ grade p (k * M) = prescribedZPower T bZ grade q M := by
    intro M
    exact transport (p.length (k * M)) (q.length M) (hlen M) _ _
      (hword (p.length (k * M)) (q.length M) (hlen M)
        (fun a ↦ p.count a * (k * M)) (fun a ↦ q.count a * M) (hcnt M)) _ _
  obtain ⟨hV, hseq⟩ := h
  refine ⟨hV, ?_⟩
  intro v hv hvV cutoff
  obtain ⟨M, hM1, hM2, hM3⟩ := hseq v hv hvV cutoff
  have hMk : M ≤ k * M := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [add_mul, one_mul]
    exact Nat.le_add_left _ _
  refine ⟨k * M, le_trans hM1 hMk, ?_, ?_⟩
  · rw [hlen M]
    exact hM2
  · rw [hlen M, hpow M]
    exact hM3
