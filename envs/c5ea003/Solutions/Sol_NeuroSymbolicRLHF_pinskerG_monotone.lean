-- Prove2me | solution 1 for NeuroSymbolicRLHF.pinskerG_monotone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:28:36.629423+00:00
-- url     : https://prove2.me/submissions/cde84ff5-c05a-4f44-a063-0a8a39cb6f06

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFPinsker.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFPinsker
import Theorems.Thm_NeuroSymbolicRLHF_hasDerivAt_pinskerG
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







/-- The second derivative is nonnegative: `1/x ≥ 27/(x+2)³` for `x > 0`. -/
theorem pinskerG_deriv_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ 1/x - 27/(x+2)^3 := by
  have h2 : (0:ℝ) < x + 2 := by linarith
  have hkey : 27 * x ≤ (x+2)^3 := by nlinarith [sq_nonneg (x - 1), hx.le]
  rw [sub_nonneg, div_le_div_iff₀ (by positivity : (0:ℝ) < (x+2)^3) hx]
  nlinarith [hkey]





/-! ## Step 2: Pinsker's inequality on a finite alphabet -/

variable {ι : Type*} [Fintype ι]


/-! ## Step 3: the square-root alignment drift bound -/



open NeuroSymbolicRLHF in
theorem solution: MonotoneOn pinskerG (Ioi (0:ℝ)) := by
  have hconv : Convex ℝ (Ioi (0:ℝ)) := convex_Ioi 0
  refine monotoneOn_of_deriv_nonneg hconv ?_ ?_ ?_
  · intro x hx
    exact ((hasDerivAt_pinskerG (mem_Ioi.1 hx)).continuousAt).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact ((hasDerivAt_pinskerG (mem_Ioi.1 hx)).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := mem_Ioi.1 hx
    rw [(hasDerivAt_pinskerG hx0).deriv]
    exact pinskerG_deriv_nonneg hx0
