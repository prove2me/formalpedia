-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.headMass_lt_mixHeadMass_of_match
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:57:21.115076+00:00
-- url     : https://prove2.me/submissions/5fab7b8e-2f5e-47d4-b56e-57fca1d9d5ab

import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter HarmonicBulkSteeperEdge in
theorem solution {w a b c : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (hab : a < b) {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (hmatch : headMass c n m₂ = mixHeadMass w a b n m₂) :
    headMass c n m₁ < mixHeadMass w a b n m₁ := by
  classical
  have hw1' : 0 < 1 - w := sub_pos.2 hw1
  have hf : ∀ k : ℕ, 1 ≤ k → 0 < pw c k :=
    fun k hk => Real.rpow_pos_of_pos (by exact_mod_cast hk) _
  have hg : ∀ k : ℕ, 1 ≤ k → 0 < mix w a b k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    unfold mix pw
    exact add_pos (mul_pos hw1' (Real.rpow_pos_of_pos hk0 _)) (mul_pos hw0 (Real.rpow_pos_of_pos hk0 _))
  -- the likelihood ratio in logarithmic coordinates
  set ψ : ℝ → ℝ := fun x => (1 - w) * Real.exp ((c - a) * x) + w * Real.exp ((c - b) * x) with hψ
  have hρ : ∀ k : ℕ, 1 ≤ k → mix w a b k / pw c k = ψ (Real.log k) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    unfold mix pw
    rw [Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hk0,
      div_eq_iff (Real.exp_pos _).ne']
    have e1 : Real.exp ((c - a) * Real.log k) * Real.exp (Real.log k * -c)
        = Real.exp (Real.log k * -a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp ((c - b) * Real.log k) * Real.exp (Real.log k * -c)
        = Real.exp (Real.log k * -b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [hψ]
    rw [add_mul, mul_assoc, mul_assoc, e1, e2]
  -- convexity of `ψ`: a middle value never exceeds both ends
  have hexp : ∀ (α u z t : ℝ), 0 < t → t < 1 →
      Real.exp (α * (t * u + (1 - t) * z)) ≤ t * Real.exp (α * u) + (1 - t) * Real.exp (α * z) := by
    intro α u z t ht0 ht1
    have := convexOn_exp.2 (Set.mem_univ (α * u)) (Set.mem_univ (α * z)) ht0.le (by linarith)
      (by ring : t + (1 - t) = 1)
    simp only [smul_eq_mul] at this
    rw [show α * (t * u + (1 - t) * z) = t * (α * u) + (1 - t) * (α * z) by ring]
    exact this
  have hexps : ∀ (α u z t : ℝ), α ≠ 0 → u ≠ z → 0 < t → t < 1 →
      Real.exp (α * (t * u + (1 - t) * z)) < t * Real.exp (α * u) + (1 - t) * Real.exp (α * z) := by
    intro α u z t hα huz ht0 ht1
    have hne : α * u ≠ α * z := fun h => huz (mul_left_cancel₀ hα h)
    have := strictConvexOn_exp.2 (Set.mem_univ (α * u)) (Set.mem_univ (α * z)) hne ht0
      (by linarith) (by ring : t + (1 - t) = 1)
    simp only [smul_eq_mul] at this
    rw [show α * (t * u + (1 - t) * z) = t * (α * u) + (1 - t) * (α * z) by ring]
    exact this
  have hψle : ∀ u v z : ℝ, u < v → v < z → ψ v ≤ max (ψ u) (ψ z) := by
    intro u v z huv hvz
    set t := (z - v) / (z - u) with ht
    have hzu : 0 < z - u := by linarith
    have ht0 : 0 < t := div_pos (by linarith) hzu
    have ht1 : t < 1 := by rw [ht, div_lt_one hzu]; linarith
    have hv : v = t * u + (1 - t) * z := by
      rw [ht]
      field_simp
      ring
    have h1 := hexp (c - a) u z t ht0 ht1
    have h2 := hexp (c - b) u z t ht0 ht1
    have hm1 := le_max_left (ψ u) (ψ z)
    have hm2 := le_max_right (ψ u) (ψ z)
    have hcomb : ψ v ≤ t * ψ u + (1 - t) * ψ z := by
      simp only [hψ]
      rw [hv]
      nlinarith [mul_le_mul_of_nonneg_left h1 hw1'.le, mul_le_mul_of_nonneg_left h2 hw0.le]
    nlinarith
  -- index sums
  have hI : ∀ x : ℕ, Finset.Icc 1 x = Finset.Ioc 0 x := by
    intro x
    ext y
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  set Sf : ℕ → ℝ := fun x => headSum c x with hSf
  set Sg : ℕ → ℝ := fun x => mixHeadSum w a b x with hSg
  have hSfn : 0 < Sf n := by
    simp only [hSf, headSum]
    exact Finset.sum_pos (fun k hk => hf k (Finset.mem_Icc.1 hk).1)
      ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hSgn : 0 < Sg n := by
    simp only [hSg, mixHeadSum]
    exact Finset.sum_pos (fun k hk => hg k (Finset.mem_Icc.1 hk).1)
      ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  set h : ℕ → ℝ := fun k => mix w a b k * Sf n - pw c k * Sg n with hh
  have hD : ∀ x : ℕ, Sg x * Sf n - Sf x * Sg n = ∑ k ∈ Finset.Ioc 0 x, h k := by
    intro x
    simp only [hSf, hSg, hh, headSum, mixHeadSum, hI, Finset.sum_sub_distrib, Finset.sum_mul]
  have hblock : ∀ p q : ℕ, p ≤ q → q ≤ n →
      ∑ k ∈ Finset.Ioc p q, h k = (Sg q * Sf n - Sf q * Sg n) - (Sg p * Sf n - Sf p * Sg n) := by
    intro p q hpq hqn
    rw [hD, hD, ← Finset.sum_Ioc_consecutive h (Nat.zero_le p) hpq]
    ring
  -- sign of `h k` is the sign of `ψ (log k) - Sg n / Sf n`
  have hhle : ∀ k : ℕ, 1 ≤ k → (h k ≤ 0 ↔ ψ (Real.log k) ≤ Sg n / Sf n) := by
    intro k hk
    rw [← hρ k hk, div_le_div_iff₀ (hf k hk) hSfn]
    simp only [hh]
    constructor <;> intro H <;> linarith
  have hmatchD : Sg m₂ * Sf n - Sf m₂ * Sg n = 0 := by
    have hm := hmatch
    simp only [headMass, mixHeadMass] at hm
    rw [div_eq_div_iff hSfn.ne' hSgn.ne'] at hm
    simp only [hSf, hSg]
    linarith
  have hlog : ∀ i j : ℕ, 1 ≤ i → i < j → Real.log (i : ℝ) < Real.log (j : ℝ) := by
    intro i j hi hij
    exact Real.log_lt_log (by exact_mod_cast hi) (by exact_mod_cast hij)
  have hgoal : headMass c n m₁ ≤ mixHeadMass w a b n m₁ ↔
      0 ≤ Sg m₁ * Sf n - Sf m₁ * Sg n := by
    simp only [headMass, mixHeadMass]
    rw [div_le_div_iff₀ hSfn hSgn]
    simp only [hSf, hSg]
    constructor <;> intro H <;> linarith
  have hgoalS : headMass c n m₁ < mixHeadMass w a b n m₁ ↔
      0 < Sg m₁ * Sf n - Sf m₁ * Sg n := by
    simp only [headMass, mixHeadMass]
    rw [div_lt_div_iff₀ hSfn hSgn]
    simp only [hSf, hSg]
    constructor <;> intro H <;> linarith
  -- the third block contains an index with `h ≤ 0`
  obtain ⟨l, hl, hl0⟩ : ∃ l ∈ Finset.Ioc m₂ n, h l ≤ 0 := by
    have hs := hblock m₂ n h₂n.le le_rfl
    have hs0 : ∑ k ∈ Finset.Ioc m₂ n, h k = 0 := by
      rw [hs, hmatchD]
      ring
    have := Finset.exists_le_of_sum_le (s := Finset.Ioc m₂ n) (f := h) (g := fun _ => (0 : ℝ))
      ⟨n, Finset.mem_Ioc.2 ⟨h₂n, le_rfl⟩⟩ (by rw [hs0, Finset.sum_const_zero])
    simpa using this
  have hl' := Finset.mem_Ioc.1 hl
  -- strict convexity: a middle value is strictly below the larger end
  have hψlt : ∀ u v z : ℝ, u < v → v < z → ψ v < max (ψ u) (ψ z) := by
    intro u v z huv hvz
    set t := (z - v) / (z - u) with ht
    have hzu : 0 < z - u := by linarith
    have ht0 : 0 < t := div_pos (by linarith) hzu
    have ht1 : t < 1 := by rw [ht, div_lt_one hzu]; linarith
    have hv : v = t * u + (1 - t) * z := by
      rw [ht]
      field_simp
      ring
    have huz : u ≠ z := by linarith
    have hm1 := le_max_left (ψ u) (ψ z)
    have hm2 := le_max_right (ψ u) (ψ z)
    have hcomb : ψ v < t * ψ u + (1 - t) * ψ z := by
      simp only [hψ]
      rw [hv]
      by_cases hα : c - a = 0
      · have hβ : c - b ≠ 0 := by intro hβ; apply (ne_of_lt hab); linarith
        have h1 := hexp (c - a) u z t ht0 ht1
        have h2 := hexps (c - b) u z t hβ huz ht0 ht1
        nlinarith [mul_le_mul_of_nonneg_left h1 hw1'.le, mul_lt_mul_of_pos_left h2 hw0]
      · have h1 := hexps (c - a) u z t hα huz ht0 ht1
        have h2 := hexp (c - b) u z t ht0 ht1
        nlinarith [mul_lt_mul_of_pos_left h1 hw1', mul_le_mul_of_nonneg_left h2 hw0.le]
    nlinarith
  rw [hgoalS]
  by_contra hneg
  have hneg' : Sg m₁ * Sf n - Sf m₁ * Sg n ≤ 0 := not_lt.1 hneg
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ Finset.Ioc 0 m₁, h i ≤ 0 := by
    have := Finset.exists_le_of_sum_le (s := Finset.Ioc 0 m₁) (f := h) (g := fun _ => (0 : ℝ))
      ⟨1, Finset.mem_Ioc.2 ⟨Nat.one_pos, hm₁⟩⟩ (by rw [← hD, Finset.sum_const_zero]; exact hneg')
    simpa using this
  obtain ⟨j, hj, hj0⟩ : ∃ j ∈ Finset.Ioc m₁ m₂, 0 ≤ h j := by
    have hs := hblock m₁ m₂ h₁₂.le h₂n.le
    rw [hmatchD] at hs
    have := Finset.exists_le_of_sum_le (s := Finset.Ioc m₁ m₂) (f := fun _ => (0 : ℝ)) (g := h)
      ⟨m₂, Finset.mem_Ioc.2 ⟨h₁₂, le_rfl⟩⟩ (by rw [hs, Finset.sum_const_zero]; linarith)
    simpa using this
  have hi' := Finset.mem_Ioc.1 hi
  have hj' := Finset.mem_Ioc.1 hj
  have hψi := (hhle i (by omega)).1 hi0
  have hψl := (hhle l (by omega)).1 hl0
  have hmid := hψlt _ _ _ (hlog i j (by omega) (by omega)) (hlog j l (by omega) (by omega))
  have hψj : ψ (Real.log j) < Sg n / Sf n := lt_of_lt_of_le hmid (max_le hψi hψl)
  have hj1 : 1 ≤ j := by omega
  have hlt : h j < 0 := by
    have hρj := hρ j hj1
    rw [← hρj, div_lt_div_iff₀ (hf j hj1) hSfn] at hψj
    simp only [hh]
    linarith
  linarith
