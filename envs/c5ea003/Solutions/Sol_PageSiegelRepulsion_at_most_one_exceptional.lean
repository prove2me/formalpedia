-- Prove2me | solution 1 for PageSiegelRepulsion.at_most_one_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:46:26.765205+00:00
-- url     : https://prove2.me/submissions/d0976e5e-ec9c-46f4-942e-dda225827b8a

import Mathlib
import Definitions.Def_Novelty_PageSiegelRepulsion

open Real PageSiegelRepulsion in
theorem solution {ε C : ℝ} {Q₀ M : ℕ}
    (hε : 0 < ε) (hQ₀ : 2 ≤ Q₀) (hM : Q₀ ≤ M)
    (hthr : 2 * (Q₀ : ℝ) ^ (-ε) * Real.log M < C)
    {χ₁ χ₂ : QuadraticCharacter}
    (h₁ : Valid ε Q₀ M χ₁) (h₂ : Valid ε Q₀ M χ₂)
    (hrep : Repulsion C χ₁ χ₂) :
    χ₁ = χ₂ := by
  by_contra hne
  have hmin := hrep hne
  obtain ⟨⟨hq1lo, hq1hi⟩, he1⟩ := h₁
  obtain ⟨⟨hq2lo, hq2hi⟩, he2⟩ := h₂
  unfold IsExceptional at he1 he2
  have hQ : (2 : ℝ) ≤ Q₀ := by exact_mod_cast hQ₀
  have hq1 : (Q₀ : ℝ) ≤ χ₁.conductor := by exact_mod_cast hq1lo
  have hq2 : (Q₀ : ℝ) ≤ χ₂.conductor := by exact_mod_cast hq2lo
  have hq1M : (χ₁.conductor : ℝ) ≤ M := by exact_mod_cast hq1hi
  have hq2M : (χ₂.conductor : ℝ) ≤ M := by exact_mod_cast hq2hi
  -- both zeros are within `Q₀^{-ε}` of `1`
  have hr1 : (χ₁.conductor : ℝ) ^ (-ε) ≤ (Q₀ : ℝ) ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hq1 (by linarith)
  have hr2 : (χ₂.conductor : ℝ) ^ (-ε) ≤ (Q₀ : ℝ) ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hq2 (by linarith)
  have hlow : 1 - (Q₀ : ℝ) ^ (-ε) ≤ min χ₁.realZero χ₂.realZero :=
    le_min (by linarith) (by linarith)
  -- `0 < log (q₁ q₂) ≤ 2 log M`
  have hprod : (4 : ℝ) ≤ (χ₁.conductor : ℝ) * χ₂.conductor := by nlinarith
  have hL : 0 < Real.log ((χ₁.conductor : ℝ) * χ₂.conductor) := Real.log_pos (by linarith)
  have hLM : Real.log ((χ₁.conductor : ℝ) * χ₂.conductor) ≤ 2 * Real.log M := by
    have h1 : (χ₁.conductor : ℝ) * χ₂.conductor ≤ (M : ℝ) * M := by nlinarith
    have h2 := Real.log_le_log (by linarith) h1
    have hMM : Real.log ((M : ℝ) * M) = 2 * Real.log M := by
      rw [Real.log_mul (by linarith) (by linarith)]
      ring
    linarith
  have hP : 0 ≤ (Q₀ : ℝ) ^ (-ε) := Real.rpow_nonneg (by linarith) _
  -- repulsion then forces `C ≤ 2 Q₀^{-ε} log M`
  have hC : C / Real.log ((χ₁.conductor : ℝ) * χ₂.conductor) ≤ (Q₀ : ℝ) ^ (-ε) := by
    linarith
  rw [div_le_iff₀ hL] at hC
  have h3 : (Q₀ : ℝ) ^ (-ε) * Real.log ((χ₁.conductor : ℝ) * χ₂.conductor)
      ≤ (Q₀ : ℝ) ^ (-ε) * (2 * Real.log M) := mul_le_mul_of_nonneg_left hLM hP
  linarith
