-- Prove2me | solution 1 for mme_Ctensor_outer_inner_balanced_weight_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:58:23.124817+00:00
-- url     : https://prove2.me/submissions/141ba7cc-1eee-47b8-b439-508361446208

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_mme_Ctensor_balanced_word_card_coarse_lower
import Theorems.Thm_mme_Ctensor_balanced_count_matching_sqrt_loss

open BigOperators Filter

set_option autoImplicit false

/-- A balanced outer type class costs only a fixed square-root exponential.
The multiplicity of each outer letter is itself `H * m`, matching the inner
balanced extraction used below. -/
private theorem outer_balanced_word_count_sqrt_loss
    (A H : ℕ) (hA : 0 < A) (hH : 0 < H) :
    let n : ℕ := A ^ 3
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let r : ℕ := H * m
        let R : ℕ := n * r
        let W : ℕ :=
          Nat.card
            {w : Fin R → Fin n // ∀ p,
              Fintype.card {j // w j = p} = r}
        (n : ℝ) ^ R *
            Real.exp (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
          (W : ℝ) := by
  dsimp only
  let n : ℕ := A ^ 3
  have hn : 0 < n := by
    dsimp [n]
    positivity
  let C : ℝ := 7 * (n : ℝ)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  let r : ℕ := H * m
  let R : ℕ := n * r
  let W : ℕ :=
    Nat.card
      {w : Fin R → Fin n // ∀ p,
        Fintype.card {j // w j = p} = r}
  let D : ℝ := (6 * (((r + 1 : ℕ) : ℝ))) ^ n
  let s : ℝ := Real.sqrt (((R + 1 : ℕ) : ℝ))
  have hmpos : 0 < m := by omega
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hnone : 1 ≤ n := hn
  have hrR : r ≤ R := by
    dsimp [R]
    simpa [mul_comm] using Nat.le_mul_of_pos_right r hn
  have hRp1 : 0 ≤ ((R + 1 : ℕ) : ℝ) := by positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs_one : 1 ≤ s := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ s := by
        dsimp [s]
        apply Real.sqrt_le_sqrt
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hcoarse :
      (n : ℝ) ^ R ≤ D * (W : ℝ) := by
    dsimp [D, W, R]
    exact mme_Ctensor_balanced_word_card_coarse_lower n r hn hrpos
  have hr1nonneg : 0 ≤ (r : ℝ) + 1 := by positivity
  have hs_r : Real.sqrt ((r : ℝ) + 1) ≤ s := by
    dsimp [s]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hrR 1
  have hlogr :
      Real.log ((r : ℝ) + 1) ≤ 2 * Real.sqrt ((r : ℝ) + 1) := by
    have hsqrtPos : 0 < Real.sqrt ((r : ℝ) + 1) := by positivity
    have hbasic := Real.log_le_sub_one_of_pos hsqrtPos
    rw [Real.log_sqrt hr1nonneg] at hbasic
    nlinarith
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hlogD :
      Real.log D =
        (n : ℝ) *
          (Real.log 6 + Real.log ((r : ℝ) + 1)) := by
    dsimp [D]
    rw [Real.log_pow,
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (by positivity)]
    push_cast
    ring
  have hlogSix : Real.log (6 : ℝ) ≤ 5 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hlogD_le : Real.log D ≤ C * s := by
    rw [hlogD]
    have hr_bound : Real.log ((r : ℝ) + 1) ≤ 2 * s :=
      hlogr.trans (mul_le_mul_of_nonneg_left hs_r (by norm_num))
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    have hinside :
        Real.log 6 + Real.log ((r : ℝ) + 1) ≤ 7 * s := by
      nlinarith
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hinside hnnonneg]
  have hDloss : D * Real.exp (-C * s) ≤ 1 := by
    have hDrepr : D = Real.exp (Real.log D) :=
      (Real.exp_log hDpos).symm
    rw [hDrepr, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  change
    (n : ℝ) ^ R * Real.exp (-C * s) ≤ (W : ℝ)
  calc
    (n : ℝ) ^ R * Real.exp (-C * s)
        ≤ (D * (W : ℝ)) * Real.exp (-C * s) := by
          gcongr
    _ = (W : ℝ) * (D * Real.exp (-C * s)) := by ring
    _ ≤ (W : ℝ) * 1 := by
      exact mul_le_mul_of_nonneg_left hDloss (by positivity)
    _ = (W : ℝ) := by ring

theorem solution
    (A H volume : ℕ) (hA : 0 < A) (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let n : ℕ := A ^ 3
        let r : ℕ := H * m
        let R : ℕ := n * r
        let Wouter : ℕ :=
          Nat.card
            {w : Fin R → Fin n // ∀ p,
              Fintype.card {j // w j = p} = r}
        let Winner : ℕ :=
          Nat.card
            {w : Fin r → Fin H // ∀ h,
              Fintype.card {j // w j = h} = m}
        ((((A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
              (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
            Real.exp
              (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
          ((Wouter : ℝ) *
            (((Winner : ℝ) ^ 2 *
                Real.exp
                  (-100 * Real.sqrt
                    (Real.log (((Winner + 1 : ℕ) : ℝ))))) ^ n)) *
            (((volume ^ (3 * R) : ℕ) : ℝ) ^ tau)) := by
  let n : ℕ := A ^ 3
  have hn : 0 < n := by
    dsimp [n]
    positivity
  obtain ⟨Couter, hCouter, houter⟩ :=
    outer_balanced_word_count_sqrt_loss A H hA hH
  dsimp only at houter
  obtain ⟨Cinner, hCinner, hinner⟩ :=
    mme_Ctensor_balanced_count_matching_sqrt_loss H hH
  let C : ℝ := Couter + (n : ℝ) * Cinner
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [houter, hinner] with m hmouter hminner
  dsimp only at hmouter hminner ⊢
  let r : ℕ := H * m
  let R : ℕ := n * r
  let Wouter : ℕ :=
    Nat.card
      {w : Fin R → Fin n // ∀ p,
        Fintype.card {j // w j = p} = r}
  let Winner : ℕ :=
    Nat.card
      {w : Fin r → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}
  let sR : ℝ := Real.sqrt (((R + 1 : ℕ) : ℝ))
  let sr : ℝ := Real.sqrt (((r + 1 : ℕ) : ℝ))
  let I : ℝ :=
    (Winner : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log (((Winner + 1 : ℕ) : ℝ))))
  let q : ℝ := (((volume ^ (3 * R) : ℕ) : ℝ) ^ tau)
  have hnone : 1 ≤ n := hn
  have hrR : r ≤ R := by
    dsimp [R]
    simpa [mul_comm] using Nat.le_mul_of_pos_right r hn
  have hsrR : sr ≤ sR := by
    dsimp [sr, sR]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hrR 1
  have hmouter' :
      (n : ℝ) ^ R * Real.exp (-Couter * sR) ≤ (Wouter : ℝ) := by
    simpa [n, r, R, Wouter, sR] using hmouter
  have hminner' :
      (H : ℝ) ^ (2 * r) * Real.exp (-Cinner * sr) ≤ I := by
    simpa [r, Winner, sr, I] using hminner
  have hinnerpow :
      ((H : ℝ) ^ (2 * r) * Real.exp (-Cinner * sr)) ^ n ≤ I ^ n :=
    pow_le_pow_left₀ (by positivity) hminner' n
  have hexpInner :
      Real.exp (-((n : ℝ) * Cinner) * sR) ≤
        (Real.exp (-Cinner * sr)) ^ n := by
    calc
      Real.exp (-((n : ℝ) * Cinner) * sR)
          ≤ Real.exp (-((n : ℝ) * Cinner) * sr) := by
            apply Real.exp_le_exp.mpr
            have hnC : 0 ≤ (n : ℝ) * Cinner := by positivity
            nlinarith
      _ = (Real.exp (-Cinner * sr)) ^ n := by
        rw [← Real.exp_nat_mul]
        push_cast
        congr 1
        ring
  have hinnerR :
      (H : ℝ) ^ (2 * R) *
          Real.exp (-((n : ℝ) * Cinner) * sR) ≤ I ^ n := by
    calc
      (H : ℝ) ^ (2 * R) *
            Real.exp (-((n : ℝ) * Cinner) * sR)
          ≤ (H : ℝ) ^ (2 * R) *
              (Real.exp (-Cinner * sr)) ^ n := by
            exact mul_le_mul_of_nonneg_left hexpInner (by positivity)
      _ = ((H : ℝ) ^ (2 * r) *
              Real.exp (-Cinner * sr)) ^ n := by
            rw [mul_pow]
            congr 1
            simp [R, pow_mul, mul_assoc, mul_comm, mul_left_comm]
      _ ≤ I ^ n := hinnerpow
  have hsplitExp :
      Real.exp (-C * sR) =
        Real.exp (-Couter * sR) *
          Real.exp (-((n : ℝ) * Cinner) * sR) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [C]
    ring
  have hcount :
      ((n : ℝ) ^ R * (H : ℝ) ^ (2 * R)) *
          Real.exp (-C * sR) ≤ (Wouter : ℝ) * I ^ n := by
    calc
      ((n : ℝ) ^ R * (H : ℝ) ^ (2 * R)) *
            Real.exp (-C * sR)
          = ((n : ℝ) ^ R * Real.exp (-Couter * sR)) *
              ((H : ℝ) ^ (2 * R) *
                Real.exp (-((n : ℝ) * Cinner) * sR)) := by
              rw [hsplitExp]
              ring
      _ ≤ (Wouter : ℝ) * I ^ n :=
        mul_le_mul hmouter' hinnerR (by positivity) (by positivity)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hvolumePow :
      ((((volume ^ 3 : ℕ) : ℝ) ^ tau) ^ R) = q := by
    dsimp [q]
    push_cast
    rw [← Real.rpow_mul_natCast (by positivity) tau R]
    rw [← Real.rpow_natCast_mul (by positivity) 3 (tau * R)]
    rw [← Real.rpow_natCast_mul (by positivity) (3 * R) tau]
    congr 1
    push_cast
    ring
  have hbase :
      (((A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
          (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) =
        ((n : ℝ) ^ R * (H : ℝ) ^ (2 * R)) * q := by
    rw [mul_pow, mul_pow, hvolumePow]
    rw [← pow_mul]
    have hncast : (n : ℝ) = (A : ℝ) ^ 3 := by
      dsimp [n]
      push_cast
      rfl
    rw [hncast]
    ring
  change
    (((A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
          (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
        Real.exp (-C * sR) ≤
      ((Wouter : ℝ) * I ^ n) * q
  rw [hbase]
  calc
    (((n : ℝ) ^ R * (H : ℝ) ^ (2 * R)) * q) *
          Real.exp (-C * sR) =
        (((n : ℝ) ^ R * (H : ℝ) ^ (2 * R)) *
          Real.exp (-C * sR)) * q := by ring
    _ ≤ ((Wouter : ℝ) * I ^ n) * q :=
      mul_le_mul_of_nonneg_right hcount hq
