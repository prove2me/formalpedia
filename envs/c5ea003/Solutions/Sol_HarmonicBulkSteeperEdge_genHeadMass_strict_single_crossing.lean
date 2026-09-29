-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.genHeadMass_strict_single_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:08:52.563565+00:00
-- url     : https://prove2.me/submissions/37dfe746-c83c-40a6-9302-3d1170dca0a3

import Mathlib
import Definitions.Def_Probability_GeneralMixtureWindowLaw
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter HarmonicBulkSteeperEdge in
theorem solution {ι : Type*} {s : Finset ι} {w e : ι → ℝ} {c : ℝ}
    (hw : ∀ i ∈ s, 0 < w i) {p q : ι} (hp : p ∈ s) (hq : q ∈ s) (hpq : e p ≠ e q)
    {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (hmatch : headMass c n m₂ = genHeadMass s w e n m₂) :
    headMass c n m₁ < genHeadMass s w e n m₁ := by
  classical
  have hf : ∀ k : ℕ, 1 ≤ k → 0 < pw c k :=
    fun k hk => Real.rpow_pos_of_pos (by exact_mod_cast hk) _
  have hg : ∀ k : ℕ, 1 ≤ k → 0 < genKernel s w e k := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    unfold genKernel pw
    exact Finset.sum_pos (fun i hi => mul_pos (hw i hi) (Real.rpow_pos_of_pos hk0 _)) ⟨p, hp⟩
  -- the likelihood ratio in logarithmic coordinates
  set ψ : ℝ → ℝ := fun x => ∑ i ∈ s, w i * Real.exp ((c - e i) * x) with hψ
  have hρ : ∀ k : ℕ, 1 ≤ k → genKernel s w e k / pw c k = ψ (Real.log k) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    unfold genKernel pw
    simp only [Real.rpow_def_of_pos hk0]
    rw [div_eq_iff (Real.exp_pos _).ne']
    simp only [hψ]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
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
  -- index sums
  have hI : ∀ x : ℕ, Finset.Icc 1 x = Finset.Ioc 0 x := by
    intro x
    ext y
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  set Sf : ℕ → ℝ := fun x => headSum c x with hSf
  set Sg : ℕ → ℝ := fun x => genHeadSum s w e x with hSg
  have hSfn : 0 < Sf n := by
    simp only [hSf, headSum]
    exact Finset.sum_pos (fun k hk => hf k (Finset.mem_Icc.1 hk).1)
      ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hSgn : 0 < Sg n := by
    simp only [hSg, genHeadSum]
    exact Finset.sum_pos (fun k hk => hg k (Finset.mem_Icc.1 hk).1)
      ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  set h : ℕ → ℝ := fun k => genKernel s w e k * Sf n - pw c k * Sg n with hh
  have hD : ∀ x : ℕ, Sg x * Sf n - Sf x * Sg n = ∑ k ∈ Finset.Ioc 0 x, h k := by
    intro x
    simp only [hSf, hSg, hh, headSum, genHeadSum, hI, Finset.sum_sub_distrib, Finset.sum_mul]
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
    simp only [headMass, genHeadMass] at hm
    rw [div_eq_div_iff hSfn.ne' hSgn.ne'] at hm
    simp only [hSf, hSg]
    linarith
  have hlog : ∀ i j : ℕ, 1 ≤ i → i < j → Real.log (i : ℝ) < Real.log (j : ℝ) := by
    intro i j hi hij
    exact Real.log_lt_log (by exact_mod_cast hi) (by exact_mod_cast hij)
  have hgoal : headMass c n m₁ ≤ genHeadMass s w e n m₁ ↔
      0 ≤ Sg m₁ * Sf n - Sf m₁ * Sg n := by
    simp only [headMass, genHeadMass]
    rw [div_le_div_iff₀ hSfn hSgn]
    simp only [hSf, hSg]
    constructor <;> intro H <;> linarith
  have hgoalS : headMass c n m₁ < genHeadMass s w e n m₁ ↔
      0 < Sg m₁ * Sf n - Sf m₁ * Sg n := by
    simp only [headMass, genHeadMass]
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
      have hr : t * ψ u + (1 - t) * ψ z
          = ∑ i ∈ s, w i * (t * Real.exp ((c - e i) * u) + (1 - t) * Real.exp ((c - e i) * z)) := by
        simp only [hψ, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hr]
      simp only [hψ]
      rw [hv]
      apply Finset.sum_lt_sum
      · intro i hi
        exact mul_le_mul_of_nonneg_left (hexp (c - e i) u z t ht0 ht1) (hw i hi).le
      · by_cases hcp : c - e p = 0
        · have hcq : c - e q ≠ 0 := by
            intro hcq
            apply hpq
            linarith
          exact ⟨q, hq, mul_lt_mul_of_pos_left (hexps (c - e q) u z t hcq huz ht0 ht1) (hw q hq)⟩
        · exact ⟨p, hp, mul_lt_mul_of_pos_left (hexps (c - e p) u z t hcp huz ht0 ht1) (hw p hp)⟩
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
