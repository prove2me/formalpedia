-- Prove2me | solution 1 for EdgeSpikeDefect.single_law_separation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T07:25:25.78384+00:00
-- url     : https://prove2.me/submissions/c5d72f1c-3de1-4d10-a38d-7795b6c5bf55

import Mathlib
import Definitions.Def_MachineLearning_EdgeSpikeKernelDefect

open EdgeSpikeDefect Real in
theorem solution {r rho : ℝ} {r' : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (hr0' : 0 ≤ r') (hr1' : r' ≤ 1) :
    rho * (1 - rho) / 84 ≤
      max |mixBin rho r 0 - geomBin r' 0|
        (max |mixBin rho r 1 - geomBin r' 1| |mixBin rho r 2 - geomBin r' 2|) := by
  have hS : 1 ≤ 1 + r + r ^ 2 := by nlinarith
  have hS' : 1 ≤ 1 + r' + r' ^ 2 := by nlinarith
  -- bin values
  have hg : ∀ j, geomBin r j = r ^ j / (1 + r + r ^ 2) := fun j => rfl
  have hq : ∀ j, geomBin r' j = r' ^ j / (1 + r' + r' ^ 2) := fun j => rfl
  have hgle : ∀ j : ℕ, 0 ≤ geomBin r j ∧ geomBin r j ≤ 1 := by
    intro j
    rw [hg]
    have h1 : r ^ j ≤ 1 := pow_le_one₀ hr0 (by linarith)
    exact ⟨div_nonneg (pow_nonneg hr0 j) (by linarith),
      (div_le_one (by linarith)).2 (by linarith)⟩
  have hqle : ∀ j : ℕ, 0 ≤ geomBin r' j ∧ geomBin r' j ≤ 1 := by
    intro j
    rw [hq]
    have h1 : r' ^ j ≤ 1 := pow_le_one₀ hr0' hr1'
    exact ⟨div_nonneg (pow_nonneg hr0' j) (by linarith),
      (div_le_one (by linarith)).2 (by linarith)⟩
  have hm : ∀ j, mixBin rho r j = (1 - rho) / 3 + rho * geomBin r j := fun j => rfl
  have hmlo : ∀ j : ℕ, (1 - rho) / 3 ≤ mixBin rho r j := by
    intro j
    rw [hm]
    have := (hgle j).1
    nlinarith
  have hmhi : ∀ j : ℕ, mixBin rho r j ≤ 1 := by
    intro j
    rw [hm]
    have := (hgle j).2
    nlinarith
  -- the pure geometric law has zero log-convexity defect
  have hqdef : geomBin r' 0 * geomBin r' 2 - geomBin r' 1 ^ 2 = 0 := by
    rw [hq, hq, hq]
    field_simp
    ring
  -- the mixture has defect at least `rho (1 - rho) / 21`
  have hmdef_eq : mixBin rho r 0 * mixBin rho r 2 - mixBin rho r 1 ^ 2
      = (1 - rho) / 3 * rho * ((1 - r) ^ 2 / (1 + r + r ^ 2)) := by
    rw [hm, hm, hm, hg, hg, hg]
    field_simp
    ring
  have hcurv : 1 / 7 ≤ (1 - r) ^ 2 / (1 + r + r ^ 2) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : 2 * r - 1 ≤ 0)
      (by linarith : r - 2 ≤ 0)]
  have hmdef : rho * (1 - rho) / 21 ≤ mixBin rho r 0 * mixBin rho r 2 - mixBin rho r 1 ^ 2 := by
    rw [hmdef_eq]
    have hc : 0 ≤ (1 - rho) / 3 * rho := by
      have : 0 ≤ 1 - rho := by linarith
      positivity
    nlinarith
  -- if all three bins were within `δ`, the defects would differ by less than `4δ`
  by_contra hlt
  have hlt' := lt_of_not_ge hlt
  set δ := rho * (1 - rho) / 84 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < 1 - rho := by linarith
    positivity
  obtain ⟨h0, h12⟩ := max_lt_iff.1 hlt'
  obtain ⟨h1, h2⟩ := max_lt_iff.1 h12
  obtain ⟨h0l, h0u⟩ := abs_lt.1 h0
  obtain ⟨h1l, h1u⟩ := abs_lt.1 h1
  obtain ⟨h2l, h2u⟩ := abs_lt.1 h2
  have hm2pos : 0 < mixBin rho r 2 := lt_of_lt_of_le (by linarith) (hmlo 2)
  have hm1pos : 0 < mixBin rho r 1 := lt_of_lt_of_le (by linarith) (hmlo 1)
  have a1 : (mixBin rho r 0 - geomBin r' 0) * mixBin rho r 2 < δ * mixBin rho r 2 :=
    mul_lt_mul_of_pos_right h0u hm2pos
  have a2 : δ * mixBin rho r 2 ≤ δ := mul_le_of_le_one_right hδ0.le (hmhi 2)
  have a3 : geomBin r' 0 * (mixBin rho r 2 - geomBin r' 2) ≤ geomBin r' 0 * δ :=
    mul_le_mul_of_nonneg_left h2u.le (hqle 0).1
  have a4 : geomBin r' 0 * δ ≤ δ := mul_le_of_le_one_left hδ0.le (hqle 0).2
  have hsum1 : 0 < mixBin rho r 1 + geomBin r' 1 := by linarith [(hqle 1).1]
  have a5 : -δ * (mixBin rho r 1 + geomBin r' 1)
      < (mixBin rho r 1 - geomBin r' 1) * (mixBin rho r 1 + geomBin r' 1) :=
    mul_lt_mul_of_pos_right h1l hsum1
  have a6 : mixBin rho r 1 + geomBin r' 1 ≤ 2 := by linarith [hmhi 1, (hqle 1).2]
  have e1 : mixBin rho r 0 * mixBin rho r 2 - geomBin r' 0 * geomBin r' 2
      = (mixBin rho r 0 - geomBin r' 0) * mixBin rho r 2
        + geomBin r' 0 * (mixBin rho r 2 - geomBin r' 2) := by ring
  have e2 : mixBin rho r 1 ^ 2 - geomBin r' 1 ^ 2
      = (mixBin rho r 1 - geomBin r' 1) * (mixBin rho r 1 + geomBin r' 1) := by ring
  nlinarith
