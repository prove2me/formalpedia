-- Prove2me | solution 1 for mme_global_CW_counted_log_copy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:00:34.65073+00:00
-- url     : https://prove2.me/submissions/d7d69650-8f6d-4090-b10b-50cde66f9d7f

import Definitions.Def_mme_global_CW_counted_stage
open BigOperators MME MME.GlobalCW
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem rounded_copies (x a : ℝ) (b : ℕ) (hb : 0 < b)
    (ha : 0 ≤ a) (hx : 2 * (b : ℝ) * Real.exp a ≤ x) :
    ⌈Real.exp a⌉₊ ≤ ⌈x⌉₊ / b := by
  have he : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  have hc : (⌈Real.exp a⌉₊ : ℝ) ≤ 2 * Real.exp a := by
    have hh := Nat.ceil_le_floor_add_one (Real.exp a)
    have hf := Nat.floor_le (Real.exp_pos a).le
    have hh' : (⌈Real.exp a⌉₊ : ℝ) ≤ (⌊Real.exp a⌋₊ : ℝ) + 1 := by exact_mod_cast hh
    linarith
  apply (Nat.le_div_iff_mul_le hb).mpr
  apply (Nat.cast_le (α := ℝ)).mp
  push_cast
  calc
    (⌈Real.exp a⌉₊ : ℝ) * b ≤ (2 * Real.exp a) * b := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg b)
    _ = 2 * b * Real.exp a := by ring
    _ ≤ x := hx
    _ ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x

theorem solution {ell M : ℕ} (D : CountedStage ell M) (E : ExactStage ell M)
    (hlower : D.lower ≤ E.hash.lower) (hexponent : E.repairExponent = D.repairExponent)
    (a : ℝ) (ha : 0 ≤ a) (hbudget : a ≤ D.certifiedLogCopies) :
    ⌈Real.exp a⌉₊ ≤ E.copies := by
  have hQ : 0 < D.scale := by
    have h : D.degree+1 ≤ D.scale := le_max_left _ _
    omega
  have hT : 0 < (RecursiveXHash.target (n := D.n) D.m).card :=
    Finset.card_pos.mpr ⟨D.reference,D.reference_target⟩
  have hTR : 0 < ((RecursiveXHash.target (n := D.n) D.m).card : ℝ) := by exact_mod_cast hT
  have hb : 0 < 8 ^ D.repairExponent := by positivity
  have hbR : 0 < ((8 ^ D.repairExponent : ℕ) : ℝ) := by exact_mod_cast hb
  have hQR : (0 : ℝ) < D.scale := by exact_mod_cast hQ
  have hblog : Real.log ((8 ^ D.repairExponent : ℕ) : ℝ) = D.repairExponent * Real.log 8 := by
    rw [Nat.cast_pow]
    exact Real.log_pow 8 _
  have hbudget' : a + Real.log (64 * (D.scale : ℝ)) +
      Real.log ((8 ^ D.repairExponent : ℕ) : ℝ) ≤
        Real.log (RecursiveXHash.target (n := D.n) D.m).card - 4 * Real.sqrt (Real.log D.scale) := by
    change a ≤ _ - _ - _ - _ at hbudget
    rw [hblog]
    linarith
  have he := Real.exp_le_exp.mpr hbudget'
  rw [Real.exp_add,Real.exp_add,Real.exp_log (by positivity : (0 : ℝ) < 64 * D.scale),
    Real.exp_log hbR,sub_eq_add_neg,Real.exp_add,Real.exp_log hTR] at he
  have hx : 2 * ((8 ^ D.repairExponent : ℕ) : ℝ) * Real.exp a ≤ D.lower := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * D.scale)).mpr
    convert he using 1 <;> ring
  simpa only [ExactStage.copies,hexponent] using
    rounded_copies E.hash.lower a (8 ^ D.repairExponent) hb ha (hx.trans hlower)
