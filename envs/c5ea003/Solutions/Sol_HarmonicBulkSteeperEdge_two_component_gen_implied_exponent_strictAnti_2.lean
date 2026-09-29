-- Prove2me | solution 2 for HarmonicBulkSteeperEdge.two_component_gen_implied_exponent_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:03:10.611732+00:00
-- url     : https://prove2.me/submissions/a65c8468-463e-4cc6-aacb-73abdd098f81

import Mathlib
import Definitions.Def_Probability_GeneralMixtureWindowLaw
import Definitions.Def_Probability_HarmonicBulkSteeperEdge

open Finset Filter HarmonicBulkSteeperEdge in
theorem solution {w a b c₁ c₂ : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (hab : a < b) {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (h₁ : headMass c₁ n m₁ = mixHeadMass w a b n m₁)
    (h₂ : headMass c₂ n m₂ = mixHeadMass w a b n m₂) :
    c₂ < c₁ := by
  have h95 : ∀ c : ℝ, headMass c n m₂ = mixHeadMass w a b n m₂ →
      headMass c n m₁ < mixHeadMass w a b n m₁ := by
    intro c hmatch
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
  -- head mass is strictly increasing in the exponent
  have hmono : ∀ c c' : ℝ, c < c' → headMass c n m₁ < headMass c' n m₁ := by
    intro c c' hcc
    unfold headMass
    rw [div_lt_div_iff₀ (hSpos c n (by omega)) (hSpos c' n (by omega))]
    unfold headSum
    apply hMLR (fun k => pw c k) (fun k => pw c' k) m₁ n hm₁ (by omega)
    intro k l hk hkl
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (lt_of_lt_of_le hk hkl.le)
    have hlog := Real.log_lt_log hk0 (show (k : ℝ) < l by exact_mod_cast hkl)
    show pw c k * pw c' l < pw c' k * pw c l
    unfold pw
    rw [Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hl0, Real.rpow_def_of_pos hk0,
      Real.rpow_def_of_pos hl0, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_lt_exp.2
    nlinarith [mul_pos (sub_pos.2 hcc) (sub_pos.2 hlog)]
  by_contra hle
  have hle' : c₁ ≤ c₂ := not_lt.1 hle
  have hA := h95 c₂ h₂
  rw [← h₁] at hA
  rcases eq_or_lt_of_le hle' with heq | hlt
  · rw [heq] at hA
    exact lt_irrefl _ hA
  · have := hmono c₁ c₂ hlt
    linarith
