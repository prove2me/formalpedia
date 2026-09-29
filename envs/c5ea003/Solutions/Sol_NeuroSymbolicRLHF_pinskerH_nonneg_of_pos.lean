-- Prove2me | solution 1 for NeuroSymbolicRLHF.pinskerH_nonneg_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:30:22.775077+00:00
-- url     : https://prove2.me/submissions/2cd594ee-c7ea-4b51-a32f-57508851d2da

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFPinsker.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFPinsker
import Theorems.Thm_NeuroSymbolicRLHF_hasDerivAt_pinskerH
import Theorems.Thm_NeuroSymbolicRLHF_pinskerG_monotone
/-
Copyright (c) 2025. All rights reserved.

# Pinsker's Inequality for Finite Alphabets, and the Square-Root Alignment Drift Bound

Fifth research cycle.  This file closes "Conjecture 1" of the previous cycle's
`FUTURE_DIRECTIONS.md`: the exponential drift bound `e^{Δ/β} - 1` proved in
`Catalog.Shared.NeuroSymbolicRLHFRobustness` is replaced by the correct
square-root rate.

The route is the classical Cauchy–Schwarz proof of Pinsker's inequality, built
here from scratch (Mathlib has no finite-alphabet Pinsker inequality at this
commit):

1. a sharp one-variable estimate `x log x - x + 1 ≥ 3(x-1)²/(2(x+2))` on
   `[0, ∞)`, proved by a second-derivative argument (`(x+2)³ ≥ 27x`);
2. its homogeneous form `a log (a/b) - a + b ≥ 3(a-b)²/(2(a+2b))`;
3. Cauchy–Schwarz against the weights `w i = p i + 2 q i`, whose total mass is
   exactly `3`.

The alignment corollary: the aligned policy satisfies
`‖π* - π_SFT‖₁ ≤ √(2(max r - min r)/β)`, which beats the exponential bound
whenever the reward range exceeds the KL coefficient — the regime of practical
RLHF.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators Set

noncomputable section

open NeuroSymbolicRLHF

/-! ## Step 1: the one-variable estimate -/





theorem pinskerG_one : pinskerG 1 = 0 := by
  unfold pinskerG
  norm_num

theorem pinskerH_one : pinskerH 1 = 0 := by
  unfold pinskerH
  norm_num






/-! ## Step 2: Pinsker's inequality on a finite alphabet -/

variable {ι : Type*} [Fintype ι]


/-! ## Step 3: the square-root alignment drift bound -/



open NeuroSymbolicRLHF in
theorem solution{x : ℝ} (hx : 0 < x) : 0 ≤ pinskerH x := by
  rcases le_total 1 x with h1 | h1
  · -- on `[1, ∞)` the derivative `pinskerG` is nonnegative, so `pinskerH` increases
    have hmono : MonotoneOn pinskerH (Ici (1:ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
      · intro y hy
        have hy0 : 0 < y := lt_of_lt_of_le one_pos (mem_Ici.1 hy)
        exact ((hasDerivAt_pinskerH hy0).continuousAt).continuousWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy0 : 0 < y := lt_trans one_pos (mem_Ioi.1 hy)
        exact ((hasDerivAt_pinskerH hy0).differentiableAt).differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        have hy1 : (1:ℝ) < y := mem_Ioi.1 hy
        have hy0 : 0 < y := lt_trans one_pos hy1
        rw [(hasDerivAt_pinskerH hy0).deriv]
        have := pinskerG_monotone (mem_Ioi.2 one_pos) (mem_Ioi.2 hy0) hy1.le
        rw [pinskerG_one] at this
        exact this
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 h1) h1
    rwa [pinskerH_one] at this
  · -- on `(0, 1]` the derivative is nonpositive, so `pinskerH` decreases to `0`
    have hanti : AntitoneOn pinskerH (Ioc (0:ℝ) 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) ?_ ?_ ?_
      · intro y hy
        exact ((hasDerivAt_pinskerH (mem_Ioc.1 hy).1).continuousAt).continuousWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        exact ((hasDerivAt_pinskerH (mem_Ioo.1 hy).1).differentiableAt).differentiableWithinAt
      · intro y hy
        rw [interior_Ioc] at hy
        obtain ⟨hy0, hy1⟩ := mem_Ioo.1 hy
        rw [(hasDerivAt_pinskerH hy0).deriv]
        have := pinskerG_monotone (mem_Ioi.2 hy0) (mem_Ioi.2 one_pos) hy1.le
        rw [pinskerG_one] at this
        exact this
    have := hanti (mem_Ioc.2 ⟨hx, h1⟩) (mem_Ioc.2 ⟨one_pos, le_rfl⟩) h1
    rwa [pinskerH_one] at this
