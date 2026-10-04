-- Prove2me | solution 3 for riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-03T19:26:59.146707+00:00
-- url     : https://prove2.me/submissions/17e4f1d5-3422-465d-9479-7964e71b1993
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_half_lt
import Theorems.Thm_summatory_isBigO_rpow_of_dirichlet_partialSum_tendsto
import Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (↑n + 1)) →
      s ≠ 1 →
      s.re = 1 / 2 := by
  have hM : ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by
    intro ε hε
    obtain ⟨L, hL⟩ := moebius_dirichlet_partialSum_tendsto_of_half_lt (1 / 2 + ε) (by linarith)
    refine summatory_isBigO_rpow_of_dirichlet_partialSum_tendsto
      (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 / 2 + ε) (by linarith) (L : ℂ) ?_
    have h2 := (Complex.continuous_ofReal.tendsto L).comp hL
    refine h2.congr fun N => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  intro s hz hnt h1
  have strip (ε : ℝ) (hε : 0 < ε) :
      1 - (1 / 2 + ε) ≤ s.re ∧ s.re ≤ 1 / 2 + ε :=
    nontrivial_zero_strip_of_moebius_summatory_power_bound
      (by linarith) (hM ε hε) hz hnt h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hb := strip ((1 / 2 - s.re) / 2) (by linarith)
    linarith [hb.1]
  · have hb := strip ((s.re - 1 / 2) / 2) (by linarith)
    linarith [hb.2]
