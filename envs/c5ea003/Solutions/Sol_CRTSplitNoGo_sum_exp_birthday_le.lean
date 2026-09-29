-- Prove2me | solution 1 for CRTSplitNoGo.sum_exp_birthday_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:59:32.684897+00:00
-- url     : https://prove2.me/submissions/b50efab9-d28a-4737-8476-5e7592bbe423

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthdayTail
open CRTSplitNoGo Finset in
theorem solution (n : ℕ) (hn : 0 < n) :
    ∑ T ∈ Finset.range n, Real.exp (-((T * (T + 1) : ℝ) / (2 * n)))
      ≤ 3 * ((Nat.sqrt n : ℝ) + 1) := by
  set s := Nat.sqrt n + 1 with hs
  have hs0 : 0 < s := Nat.succ_pos _
  have hsq : n < s * s := Nat.lt_succ_sqrt n
  set r := Real.exp (-(1 / 2 : ℝ)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  -- `e^{-1/2} ≤ 2/3` because `e^{1/2} ≥ 3/2`
  have hr1 : r ≤ 2 / 3 := by
    have h := Real.add_one_le_exp (1 / 2 : ℝ)
    have hm : Real.exp (1 / 2) * r = 1 := by rw [hr, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  -- termwise: `T(T+1) ≥ ⌊T/s⌋·n`, so each term is at most `r^⌊T/s⌋`
  have hterm : ∀ T : ℕ, Real.exp (-((T * (T + 1) : ℝ) / (2 * n))) ≤ r ^ (T / s) := by
    intro T
    rw [hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hkT : T / s * s ≤ T := Nat.div_mul_le_self T s
    have hkN : T / s * n ≤ T * (T + 1) := by
      rcases Nat.eq_zero_or_pos (T / s) with h0 | h0
      · rw [h0, zero_mul]
        exact Nat.zero_le _
      · have hsT : s ≤ T := le_trans (Nat.le_mul_of_pos_left s h0) hkT
        calc T / s * n ≤ T / s * (s * s) := Nat.mul_le_mul_left _ hsq.le
          _ = (T / s * s) * s := by ring
          _ ≤ T * s := Nat.mul_le_mul_right _ hkT
          _ ≤ T * T := Nat.mul_le_mul_left _ hsT
          _ ≤ T * (T + 1) := Nat.mul_le_mul_left _ (Nat.le_succ T)
    have hkNr : ((T / s : ℕ) : ℝ) * n ≤ (T : ℝ) * (T + 1) := by exact_mod_cast hkN
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have e : ((T / s : ℕ) : ℝ) * (-(1 / 2 : ℝ)) = -(((T / s : ℕ) : ℝ) * n / (2 * n)) := by
      field_simp
    rw [e, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right hkNr (by positivity)
  -- group the indices into blocks of length `s`
  have hgroup : ∀ K : ℕ, ∑ T ∈ range (s * K), r ^ (T / s) = (s : ℝ) * ∑ k ∈ range K, r ^ k := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Nat.mul_succ, sum_range_add, ih, Finset.sum_range_succ (fun k => r ^ k) K, mul_add]
      congr 1
      rw [sum_congr rfl (fun j hj => by
        rw [Nat.mul_add_div hs0, Nat.div_eq_of_lt (mem_range.mp hj), add_zero])]
      rw [sum_const, card_range, nsmul_eq_mul]
  -- geometric tail: `Σ_{k<n} r^k ≤ 1/(1-r) ≤ 3`
  have hgeom : ∑ k ∈ range n, r ^ k ≤ 3 := by
    have hr1' : r ≠ 1 := by
      intro h
      rw [h] at hr1
      norm_num at hr1
    rw [geom_sum_eq hr1', div_le_iff_of_neg (by linarith)]
    nlinarith [pow_nonneg hr0 n]
  calc ∑ T ∈ range n, Real.exp (-((T * (T + 1) : ℝ) / (2 * n)))
      ≤ ∑ T ∈ range n, r ^ (T / s) := sum_le_sum (fun T _ => hterm T)
    _ ≤ ∑ T ∈ range (s * n), r ^ (T / s) :=
        sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_mul_of_pos_left n hs0))
          (fun _ _ _ => pow_nonneg hr0 _)
    _ = (s : ℝ) * ∑ k ∈ range n, r ^ k := hgroup n
    _ ≤ (s : ℝ) * 3 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 3 * ((Nat.sqrt n : ℝ) + 1) := by rw [hs]; push_cast; ring
