-- Prove2me | solution 1 for riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T11:02:29.35901+00:00
-- url     : https://prove2.me/submissions/a21cf459-9f1f-4757-8639-4191affde68c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_zeta_nontrivial_zero_mem_critical_strip
import Theorems.Thm_zeta_zero_one_sub_of_mem_critical_strip
import Theorems.Thm_zeta_ne_zero_of_half_lt_re

theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
      s ≠ 1 →
      s.re = 1 / 2 := by
  intro s hz htriv hs1
  obtain ⟨h0, h1⟩ := zeta_nontrivial_zero_mem_critical_strip s hz htriv hs1
  have hle : s.re ≤ 1 / 2 := by
    by_contra h
    push_neg at h
    exact zeta_ne_zero_of_half_lt_re s h hz
  have hz' : riemannZeta (1 - s) = 0 :=
    zeta_zero_one_sub_of_mem_critical_strip s h0 h1 hz
  have hge : (1 - s).re ≤ 1 / 2 := by
    by_contra h
    push_neg at h
    exact zeta_ne_zero_of_half_lt_re (1 - s) h hz'
  simp only [Complex.sub_re, Complex.one_re] at hge
  linarith
