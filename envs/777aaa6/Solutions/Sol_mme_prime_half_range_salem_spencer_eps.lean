-- Prove2me | solution 1 for mme_prime_half_range_salem_spencer_eps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T13:41:44.865852+00:00
-- url     : https://prove2.me/submissions/6a9733b8-e11d-4441-ab6b-55cf6a9cb388

import Theorems.Thm_mme_salem_spencer_eps_form
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Real
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000

namespace MME.DWZB2Hash

/-- The half-range costs no fixed positive power of the modulus. -/
theorem half_range_set_eps (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ P₀ : ℕ, ∀ p : ℕ, P₀ ≤ p →
      ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧ (p : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) := by
  obtain ⟨Q₀, hQ₀⟩ := mme_salem_spencer_eps_form (ε / 2) (by positivity)
  obtain ⟨L, hL⟩ := exists_nat_ge ((3 : ℝ) ^ (2 / ε))
  refine ⟨2 * max Q₀ (max L 1) + 2, ?_⟩
  intro p hp
  let Q := p / 2
  have hQQ : Q₀ ≤ Q := by dsimp [Q]; omega
  have hQL : L ≤ Q := by dsimp [Q]; omega
  have hQpos : 0 < Q := by dsimp [Q]; omega
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hpQ : (p : ℝ) ≤ 3 * (Q : ℝ) := by
    have hnat : p ≤ 3 * Q := by dsimp [Q]; omega
    exact_mod_cast hnat
  have hbase : (3 : ℝ) ^ (2 / ε) ≤ (Q : ℝ) :=
    hL.trans (by exact_mod_cast hQL)
  have hpower : (3 : ℝ) ≤ (Q : ℝ) ^ (ε / 2) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 3 ^ (2 / ε))
      hbase (by positivity : 0 ≤ ε / 2)
    have hexp : (2 / ε) * (ε / 2) = 1 := by field_simp [ne_of_gt hε]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), hexp, Real.rpow_one] at h
    exact h
  obtain ⟨S, hS, hfree, hsize⟩ := hQ₀ Q hQQ
  refine ⟨S, hS, hfree, le_trans ?_ hsize⟩
  calc
    (p : ℝ) ^ (1 - ε) ≤ (3 * (Q : ℝ)) ^ (1 - ε) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hpQ (by linarith)
    _ = (3 : ℝ) ^ (1 - ε) * (Q : ℝ) ^ (1 - ε) :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 3 * (Q : ℝ) ^ (1 - ε) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (show 1 - ε ≤ 1 by linarith)
    _ ≤ (Q : ℝ) ^ (ε / 2) * (Q : ℝ) ^ (1 - ε) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (Q : ℝ) ^ (1 - ε / 2) := by
      rw [← Real.rpow_add hQreal]
      congr 1
      ring

/-- A prime of constant-factor size with a near-linear progression-free half-range set. -/
theorem prime_half_range_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧ B < p ∧ p ≤ 2 * B ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧ 0 < S.card ∧
          (p : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) := by
  let δ := min ε (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨P₀, hP₀⟩ := half_range_set_eps δ hδ hδ1
  refine ⟨max P₀ 8, ?_⟩
  intro B hB
  have hB8 : 8 ≤ B := le_trans (le_max_right _ _) hB
  obtain ⟨p, hp, hBp, hpB⟩ := Nat.exists_prime_lt_and_le_two_mul B (by omega)
  have hp8 : 8 < p := lt_of_le_of_lt hB8 hBp
  obtain ⟨S, hS, hfree, hsize⟩ := hP₀ p
    (le_trans (le_trans (le_max_left _ _) hB) hBp.le)
  have hsize' : (p : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le)
      (by have := min_le_left ε (1 / 2 : ℝ); dsimp [δ]; linarith)) hsize
  have hcard : 0 < S.card := by
    have : (0 : ℝ) < S.card := lt_of_lt_of_le
      (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _) hsize'
    exact_mod_cast this
  exact ⟨p, hp, hp.odd_of_ne_two (by omega), hp8, hBp, hpB,
    S, hS, hfree, hcard, hsize'⟩

end MME.DWZB2Hash

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧ B < p ∧ p ≤ 2 * B ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧ 0 < S.card ∧
          (p : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) := by
  exact MME.DWZB2Hash.prime_half_range_eps ε hε
