-- Prove2me | solution 1 for Erdos183.log_le_paletteLogWidth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:27:27.65675+00:00
-- url     : https://prove2.me/submissions/ad9a61af-8736-48f2-b681-5419cf7e6200

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution (H : ℕ) :
    Real.log (H : ℝ) ≤ (paletteLogWidth H : ℝ) := by
  calc
    Real.log (H : ℝ) ≤ (⌈Real.log (H : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ ≤ (paletteLogWidth H : ℝ) := by
      exact_mod_cast (Nat.le_max_right 2 ⌈Real.log (H : ℝ)⌉₊)
