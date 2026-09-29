-- Prove2me | solution 1 for moebius_summatory_rpow_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T19:54:51.289392+00:00
-- url     : https://prove2.me/submissions/4b8c4cc6-f664-4430-a94b-bb806e694a66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_half_lt
import Theorems.Thm_summatory_isBigO_rpow_of_dirichlet_partialSum_tendsto

theorem solution :
    ∀ ε : ℝ, 0 < ε →
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
