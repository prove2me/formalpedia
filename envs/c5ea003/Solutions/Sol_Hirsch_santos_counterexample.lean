-- Prove2me | solution 1 for Hirsch.santos_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T13:25:10.421434+00:00
-- url     : https://prove2.me/submissions/da4e7b1a-67b7-4d5b-bc3b-6f6ee58c9d86

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_five_spindle_length_six
import Theorems.Thm_Hirsch_strong_dstep_spindle

open scoped RealInnerProductSpace
open Hirsch

theorem solution :
    ∃ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty ∧ Bornology.IsBounded (Hpoly a b) ∧
      ¬ DiamLE (Hpoly a b) (n - d) := by
  obtain ⟨n, a, b, u, v, hn, hne, hbd, hu, hv, hsp, hlong⟩ := five_spindle_length_six
  have hd : (0 : ℕ) < 5 := by decide
  have hdn : 5 ≤ n := le_trans (by decide : 5 ≤ 25) hn
  obtain ⟨D, a', b', hD, hne', hbd', hfail⟩ :=
    strong_dstep_spindle 5 n hd hdn a b u v hne hbd hu hv hsp hlong
  refine ⟨D, 2 * D, a', b', hne', hbd', ?_⟩
  have hND : 2 * D - D = D := by omega
  simpa [hND] using hfail
