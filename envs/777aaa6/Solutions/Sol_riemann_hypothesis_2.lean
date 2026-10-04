-- Prove2me | solution 2 for riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-03T12:40:34.559394+00:00
-- url     : https://prove2.me/submissions/fad0b044-cf42-4ffb-95dc-ab7f3dc50c17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_moebius_summatory_rpow_bound
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
      s ≠ 1 →
      s.re = 1 / 2 := by
  intro s hz hnt h1
  have strip (ε : ℝ) (hε : 0 < ε) :
      1 - (1 / 2 + ε) ≤ s.re ∧ s.re ≤ 1 / 2 + ε :=
    nontrivial_zero_strip_of_moebius_summatory_power_bound
      (by linarith) (moebius_summatory_rpow_bound ε hε) hz hnt h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hb := strip ((1 / 2 - s.re) / 2) (by linarith)
    linarith [hb.1]
  · have hb := strip ((s.re - 1 / 2) / 2) (by linarith)
    linarith [hb.2]
