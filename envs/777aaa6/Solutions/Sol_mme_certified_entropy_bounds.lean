-- Prove2me | solution 1 for mme_certified_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T20:44:48.851286+00:00
-- url     : https://prove2.me/submissions/4f1e2c8d-cc32-43f4-829d-c50b9411643e

import Mathlib
import Definitions.Def_mme_certified_entropy_reference
open BigOperators MME MME.RegionRate MME.Cert
open scoped Classical
set_option autoImplicit false
universe u

namespace MME.Cert

variable {W : Type*} [Fintype W]

theorem entropy_ge (p : W → ℝ) (hp : ∀ w, 0 ≤ p w) (e : W → Fin 4 → ℤ) :
    ∑ w, (p w - (p w) ^ 2 / qval (e w) - p w * Real.log (qval (e w))) ≤ entropy p :=
  Finset.sum_le_sum fun w _ ↦ negMulLog_ge (hp w) (qval_pos (e w))

theorem entropy_le (p : W → ℝ) (hp : ∀ w, 0 ≤ p w) (e : W → Fin 4 → ℤ) :
    entropy p ≤ ∑ w, (qval (e w) - p w - p w * Real.log (qval (e w))) :=
  Finset.sum_le_sum fun w _ ↦ negMulLog_le (hp w) (qval_pos (e w))

/-- Unnormalized entropy of masses, in terms of the normalized distribution. -/
theorem massEntropy_eq (x : W → ℝ) (hS : 0 < ∑ w, x w) :
    massEntropy x = (∑ w, x w) * entropy (fun w ↦ x w / (∑ w, x w)) := by
  set S := ∑ w, x w with hSdef
  unfold massEntropy entropy
  have hterm : ∀ w, S * Real.negMulLog (x w / S) = Real.negMulLog (x w) + x w * Real.log S := by
    intro w
    rcases eq_or_ne (x w) 0 with h | h
    · simp [Real.negMulLog, h]
    · simp only [Real.negMulLog]
      rw [Real.log_div h hS.ne']
      field_simp
      ring
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun w _ ↦ hterm w), Finset.sum_add_distrib,
    ← Finset.sum_mul, ← hSdef]
  simp only [Real.negMulLog]
  ring

end MME.Cert

theorem solution :
    (∀ {W : Type u} [Fintype W] (p : W → ℝ), (∀ w, 0 ≤ p w) → ∀ e : W → Fin 4 → ℤ,
      ∑ w, (p w - (p w) ^ 2 / qval (e w) - p w * Real.log (qval (e w))) ≤ entropy p) ∧
    (∀ {W : Type u} [Fintype W] (p : W → ℝ), (∀ w, 0 ≤ p w) → ∀ e : W → Fin 4 → ℤ,
      entropy p ≤ ∑ w, (qval (e w) - p w - p w * Real.log (qval (e w)))) ∧
    ∀ {W : Type u} [Fintype W] (x : W → ℝ), 0 < ∑ w, x w →
      massEntropy x = (∑ w, x w) * entropy (fun w ↦ x w / (∑ w, x w)) :=
  ⟨fun {W} _ p hp e ↦ MME.Cert.entropy_ge p hp e,
   fun {W} _ p hp e ↦ MME.Cert.entropy_le p hp e,
   fun {W} _ x hS ↦ MME.Cert.massEntropy_eq x hS⟩
