-- Prove2me | solution 1 for Tropical.DecodingTradeoff.twoState_fixed
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:56:10.174608+00:00
-- url     : https://prove2.me/submissions/cacfec25-38f5-450e-8313-b57b7f2d8959

import Mathlib
import Definitions.Def_Tropical_DecodingTradeoff_Core

open Tropical.DecodingTradeoff Finset

theorem solution {d : ℝ} (hd : 0 ≤ d) :
    mulVec (twoState d) ![0, d] = ![0, d] := by
  ext i
  fin_cases i
  · -- coordinate 0: min(0+0, d+d) = 0
    change tmin (fun b : Fin 2 => twoState d 0 b + (![0, d] : Fin 2 → ℝ) b) = 0
    apply le_antisymm
    · -- inf ≤ value at 0
      refine (inf'_le _ (mem_univ (0 : Fin 2))).trans_eq ?_
      simp [twoState]
    · -- 0 ≤ inf: every value ≥ 0
      refine le_inf' _ _ ?_
      intro b hb
      fin_cases b <;> simp [twoState] <;> nlinarith
  · -- coordinate 1: min(d+0, 0+d) = d
    change tmin (fun b : Fin 2 => twoState d 1 b + (![0, d] : Fin 2 → ℝ) b) = d
    apply le_antisymm
    · refine (inf'_le _ (mem_univ (0 : Fin 2))).trans_eq ?_
      simp [twoState]
    · refine le_inf' _ _ ?_
      intro b hb
      fin_cases b <;> simp [twoState]
