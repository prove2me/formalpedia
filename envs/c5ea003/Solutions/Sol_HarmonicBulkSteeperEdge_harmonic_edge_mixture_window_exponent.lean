-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.harmonic_edge_mixture_window_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:15:30.254141+00:00
-- url     : https://prove2.me/submissions/0d0dd8e4-f3f1-4609-8ade-da10a49588d3

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter HarmonicBulkSteeperEdge in
theorem solution {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    ∃ c ∈ Set.Ioo (1:ℝ) 2, headMass c n m = mixHeadMass (54/127) 1 2 n m := by
  have hMLR : ∀ (f g : ℕ → ℝ) (m n : ℕ), 1 ≤ m → m < n →
      (∀ k l : ℕ, 1 ≤ k → k < l → f k * g l < g k * f l) →
      (∑ k ∈ Finset.Icc 1 m, f k) * (∑ k ∈ Finset.Icc 1 n, g k)
        < (∑ k ∈ Finset.Icc 1 m, g k) * (∑ k ∈ Finset.Icc 1 n, f k) := by
    intro f g m n hm hmn hfg
    have hI : ∀ x : ℕ, Finset.Icc 1 x = Finset.Ioc 0 x := by
      intro x
      ext y
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hI, hI, ← sub_pos]
    have hsplit : ∀ F : ℕ → ℝ, ∑ l ∈ Finset.Ioc 0 n, F l
        = ∑ l ∈ Finset.Ioc 0 m, F l + ∑ l ∈ Finset.Ioc m n, F l :=
      fun F => (Finset.sum_Ioc_consecutive F (Nat.zero_le m) hmn.le).symm
    have key : (∑ k ∈ Finset.Ioc 0 m, g k) * (∑ k ∈ Finset.Ioc 0 n, f k)
          - (∑ k ∈ Finset.Ioc 0 m, f k) * (∑ k ∈ Finset.Ioc 0 n, g k)
        = ∑ k ∈ Finset.Ioc 0 m, ∑ l ∈ Finset.Ioc m n, (g k * f l - f k * g l) := by
      rw [hsplit f, hsplit g]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    rw [key]
    apply Finset.sum_pos
    · intro k hk
      apply Finset.sum_pos
      · intro l hl
        have hk' := Finset.mem_Ioc.1 hk
        have hl' := Finset.mem_Ioc.1 hl
        have := hfg k l (by omega) (by omega)
        linarith
      · exact ⟨n, Finset.mem_Ioc.2 ⟨hmn, le_rfl⟩⟩
    · exact ⟨1, Finset.mem_Ioc.2 ⟨Nat.one_pos, hm⟩⟩
  have hSpos : ∀ (e : ℝ) (x : ℕ), 1 ≤ x → 0 < headSum e x := by
    intro e x hx
    unfold headSum
    exact Finset.sum_pos (fun k hk => Real.rpow_pos_of_pos (by
      have := (Finset.mem_Icc.1 hk).1
      exact_mod_cast this) _) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hx⟩⟩
  set w : ℝ := 54 / 127 with hw
  have hw0 : 0 < w := by norm_num [hw]
  have hw1 : 0 < 1 - w := by norm_num [hw]
  have hp1 : ∀ k : ℕ, pw 1 k = ((k : ℝ))⁻¹ := fun k => by
    unfold pw
    exact Real.rpow_neg_one _
  have hp2 : ∀ k : ℕ, pw 2 k = ((k : ℝ))⁻¹ ^ 2 := fun k => by
    unfold pw
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, inv_pow]
  have hmixk : ∀ k : ℕ, mix w 1 2 k = (1 - w) * ((k : ℝ))⁻¹ + w * ((k : ℝ))⁻¹ ^ 2 := by
    intro k
    unfold mix
    rw [hp1, hp2]
  have hinv : ∀ k l : ℕ, 1 ≤ k → k < l → 0 < ((l : ℝ))⁻¹ ∧ ((l : ℝ))⁻¹ < ((k : ℝ))⁻¹ := by
    intro k l hk hkl
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (lt_of_lt_of_le hk hkl.le)
    exact ⟨inv_pos.2 hl0, inv_strictAnti₀ hk0 (by exact_mod_cast hkl)⟩
  have hMpos : ∀ x : ℕ, 1 ≤ x → 0 < mixHeadSum w 1 2 x := by
    intro x hx
    unfold mixHeadSum
    refine Finset.sum_pos (fun k hk => ?_) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hx⟩⟩
    have hk0 : (0 : ℝ) < k := by
      have := (Finset.mem_Icc.1 hk).1
      exact_mod_cast this
    rw [hmixk]
    have := inv_pos.2 hk0
    positivity
  -- at exponent 1 the mixture is more head-heavy
  have hlow : headMass 1 n m - mixHeadMass w 1 2 n m < 0 := by
    rw [sub_neg]
    unfold headMass mixHeadMass
    rw [div_lt_div_iff₀ (hSpos 1 n (by omega)) (hMpos n (by omega))]
    unfold headSum mixHeadSum
    apply hMLR (fun k => pw 1 k) (fun k => mix w 1 2 k) m n hm hmn
    intro k l hk hkl
    obtain ⟨hy, hxy⟩ := hinv k l hk hkl
    show pw 1 k * mix w 1 2 l < mix w 1 2 k * pw 1 l
    rw [hp1, hp1, hmixk, hmixk]
    have hx : 0 < ((k : ℝ))⁻¹ := lt_trans hy hxy
    nlinarith [mul_pos (mul_pos (mul_pos hw0 hx) hy) (sub_pos.2 hxy)]
  -- at exponent 2 the pure law is more head-heavy
  have hhigh : 0 < headMass 2 n m - mixHeadMass w 1 2 n m := by
    rw [sub_pos]
    unfold headMass mixHeadMass
    rw [div_lt_div_iff₀ (hMpos n (by omega)) (hSpos 2 n (by omega))]
    unfold headSum mixHeadSum
    apply hMLR (fun k => mix w 1 2 k) (fun k => pw 2 k) m n hm hmn
    intro k l hk hkl
    obtain ⟨hy, hxy⟩ := hinv k l hk hkl
    show mix w 1 2 k * pw 2 l < pw 2 k * mix w 1 2 l
    rw [hp2, hp2, hmixk, hmixk]
    have hx : 0 < ((k : ℝ))⁻¹ := lt_trans hy hxy
    nlinarith [mul_pos (mul_pos (mul_pos hw1 hx) hy) (sub_pos.2 hxy),
      mul_pos hx hy, mul_pos (mul_pos hx hy) (mul_pos hx hy)]
  have hS : ∀ x : ℕ, Continuous (fun c : ℝ => headSum c x) := by
    intro x
    unfold headSum pw
    exact continuous_finsetSum _ (fun k hk => continuous_const.rpow continuous_neg
      (fun _ => Or.inl (Nat.cast_ne_zero.2 (by have := (Finset.mem_Icc.1 hk).1; omega))))
  have hcont : ContinuousOn (fun c : ℝ => headMass c n m - mixHeadMass w 1 2 n m)
      (Set.Icc 1 2) := by
    apply Continuous.continuousOn
    apply Continuous.sub _ continuous_const
    show Continuous fun c : ℝ => headSum c m / headSum c n
    exact (hS m).div (hS n) (fun c => (hSpos c n (by omega)).ne')
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) hcont
    (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hlow, hhigh⟩)
  exact ⟨c, hc, by simp only at hc0; linarith⟩
