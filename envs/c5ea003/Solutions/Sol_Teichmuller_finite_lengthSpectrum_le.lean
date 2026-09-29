-- Prove2me | solution 1 for Teichmuller.finite_lengthSpectrum_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T09:19:39.393633+00:00
-- url     : https://prove2.me/submissions/79d42ea0-1757-442b-b3ac-adcacc45349b

import Definitions.Def_Geometry_Teichmuller_LengthSpectrum
open Teichmuller Complex UpperHalfPlane Matrix MatrixGroups in
theorem solution (M : ℝ) :
    {r : ℝ | (∃ g : SL(2, ℤ), 2 < |tr g| ∧ r = Real.log (stretch g)) ∧ r ≤ M}.Finite := by
  have hsub : {r : ℝ | (∃ g : SL(2, ℤ), 2 < |tr g| ∧ r = Real.log (stretch g)) ∧ r ≤ M}
      ⊆ (fun n : ℤ => Real.log ((|(n : ℝ)| + Real.sqrt ((n : ℝ) ^ 2 - 4)) / 2)) ''
        Set.Icc (-⌈2 * Real.exp M⌉) ⌈2 * Real.exp M⌉ := by
    rintro r ⟨⟨g, hg, rfl⟩, hM⟩
    have htr : tr g = ((g 0 0 + g 1 1 : ℤ) : ℝ) := by
      simp [tr, entry]
    have hs0 : 0 < stretch g := by
      unfold stretch
      have := Real.sqrt_nonneg (tr g ^ 2 - 4)
      linarith
    have hsle : stretch g ≤ Real.exp M := by
      rw [← Real.exp_log hs0]
      exact Real.exp_le_exp.mpr hM
    have habs : |tr g| ≤ 2 * stretch g := by
      unfold stretch
      linarith [Real.sqrt_nonneg (tr g ^ 2 - 4)]
    refine ⟨g 0 0 + g 1 1, ?_, ?_⟩
    · have hle : |((g 0 0 + g 1 1 : ℤ) : ℝ)| ≤ ((⌈2 * Real.exp M⌉ : ℤ) : ℝ) := by
        rw [← htr]
        linarith [Int.le_ceil (2 * Real.exp M)]
      have hle' : |g 0 0 + g 1 1| ≤ ⌈2 * Real.exp M⌉ := by exact_mod_cast hle
      exact abs_le.mp hle'
    · show Real.log ((|((g 0 0 + g 1 1 : ℤ) : ℝ)| + Real.sqrt (((g 0 0 + g 1 1 : ℤ) : ℝ) ^ 2 - 4)) / 2)
        = Real.log (stretch g)
      rw [← htr]
      rfl
  exact ((Set.finite_Icc _ _).image _).subset hsub
