-- Prove2me | solution 1 for SpectralFlatness.parseval_corr
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:14:42.890382+00:00
-- url     : https://prove2.me/submissions/d44fbe77-7868-40fc-aed7-ed40e1f26d63

import Mathlib
import Definitions.Def_Novelty_WalshSpectralFlatness
import Theorems.Thm_SpectralFlatness_parseval

open Finset SpectralFlatness
set_option autoImplicit false

/- Adapted from Paul Klemstine's Aether Catalog, commit 53c2925a02,
   Catalog/Novelty/WalshSpectralFlatness.lean, lines 208–228.
   The missing IsSignFn.sq helper is proved locally as hsq. -/
theorem solution {n : ℕ} {f : (Fin n → Bool) → ℝ} (hf : IsSignFn f) :
    ∑ S ∈ (univ : Finset (Fin n)).powerset, (corr f S) ^ 2 = 1 := by
  have hp := SpectralFlatness.parseval f
  have hsq : ∀ x : Fin n → Bool, (f x) ^ 2 = 1 := by
    intro x
    rcases hf x with h | h <;> simp [h]
  simp_rw [hsq] at hp
  rw [Finset.sum_const, Finset.card_univ] at hp
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by
    simp [Fintype.card_fun]
  rw [nsmul_eq_mul, hcard] at hp
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  have : ∑ S ∈ (univ : Finset (Fin n)).powerset, (corr f S) ^ 2
      = (((2 : ℝ) ^ n)⁻¹) ^ 2 * ∑ S ∈ (univ : Finset (Fin n)).powerset, (walshSum f S) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by rw [corr]; ring
  rw [this, hp]
  field_simp
