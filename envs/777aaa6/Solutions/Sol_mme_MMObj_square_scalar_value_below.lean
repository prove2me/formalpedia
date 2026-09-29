-- Prove2me | solution 1 for mme_MMObj_square_scalar_value_below
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:55:40.883986+00:00
-- url     : https://prove2.me/submissions/a22eb09f-127f-4675-bedd-54cf51a78baa

import Definitions.Def_mme_tau_value
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_MMObj_square_kronPow_iso
import Theorems.Thm_mme_rectangular_MM_support_diagonal_block_matching
import Theorems.Thm_mme_MMObj_restrict_scalar_bigAdd_of_induced_matching
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Mathlib.Tactic

open MME BigOperators Filter
universe u
set_option autoImplicit false

private theorem power_matching_loss_bound (H N : ℕ) (hH : 0 < H) :
    Real.sqrt (Real.log (((H ^ N + 1 : ℕ) : ℝ))) ≤
      Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) *
        Real.sqrt (((N + 1 : ℕ) : ℝ)) := by
  have hn : H ^ N + 1 ≤ (H + 1) ^ (N + 1) := by
    have hpow : H ^ N ≤ (H + 1) ^ N := Nat.pow_le_pow_left (by omega) N
    have hpos : 1 ≤ (H + 1) ^ N := Nat.one_le_pow N (H + 1) (by omega)
    rw [pow_succ]
    nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((H ^ N + 1 : ℕ) : ℝ))
    (show (((H ^ N + 1 : ℕ) : ℝ)) ≤ (((H + 1) ^ (N + 1) : ℕ) : ℝ) by exact_mod_cast hn)
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hs := Real.sqrt_le_sqrt hlog
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ))] at hs
  simpa only [mul_comm] using hs

/-- Scalar blocks give every square matrix tensor every value strictly below
its squared side length, at every real exponent. -/
theorem solution {K : Type u} [Field K]
    (H : ℕ) (tau V : ℝ) (hV : 0 ≤ V) (hVH : V < (H : ℝ) ^ 2) :
    HasTauValueAtLeast (MMObj K H H H) tau V := by
  have hH : 0 < H := by
    by_contra h
    have : H = 0 := by omega
    subst H
    norm_num at hVH
    linarith
  let C : ℝ := 100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))
  have hC : 0 ≤ C := by positivity
  have hevent := mme_strict_pow_absorbs_sqrt_exp_loss V ((H : ℝ) ^ 2) C hV hVH hC
  refine ⟨hV, ?_⟩
  intro epsilon hepsilon
  apply Filter.Eventually.frequently
  filter_upwards [hevent] with N hN
  obtain ⟨E, hx, hy, hz, hind, hcard⟩ :=
    mme_rectangular_MM_support_diagonal_block_matching (H ^ N) 1 (H ^ N) (H ^ N)
      (pow_pos hH _) (by simp) (by simp)
  have hr := (mme_MMObj_restrict_scalar_bigAdd_of_induced_matching (K := K)
    (H ^ N) E hx hy hz hind).trans (mme_MMObj_square_kronPow_iso (K := K) H N).2
  refine ⟨E.card, fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ 1, hr, ?_⟩
  have hweight : (V ^ N) ≤ (E.card : ℝ) := by
    have hloss := power_matching_loss_bound H N hH
    have hexp : Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        Real.exp (-100 * Real.sqrt (Real.log (((H ^ N + 1 : ℕ) : ℝ)))) := by
      apply Real.exp_le_exp.mpr
      dsimp [C]
      nlinarith
    calc
      V ^ N ≤ ((H : ℝ) ^ 2) ^ N *
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) := hN
      _ ≤ ((H : ℝ) ^ 2) ^ N *
          Real.exp (-100 * Real.sqrt (Real.log (((H ^ N + 1 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (H ^ N : ℕ) ^ (2 : ℕ) *
          Real.exp (-100 * Real.sqrt (Real.log (((H ^ N + 1 : ℕ) : ℝ)))) := by
        push_cast
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 N]
      _ ≤ (E.card : ℝ) := by simpa using hcard
  have hsmall : V ^ N * (1 - epsilon) ≤ V ^ N :=
    mul_le_of_le_one_right (pow_nonneg hV N) (by linarith)
  simpa using hsmall.trans hweight

