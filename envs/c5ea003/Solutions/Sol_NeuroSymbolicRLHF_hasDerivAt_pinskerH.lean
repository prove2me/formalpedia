-- Prove2me | solution 1 for NeuroSymbolicRLHF.hasDerivAt_pinskerH
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:26:01.235227+00:00
-- url     : https://prove2.me/submissions/bed9fb60-c0f5-44c2-b361-ebcaa67b977a

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFPinsker.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFPinsker
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












/-! ## Step 2: Pinsker's inequality on a finite alphabet -/

variable {ι : Type*} [Fintype ι]


/-! ## Step 3: the square-root alignment drift bound -/



open NeuroSymbolicRLHF in
theorem solution{x : ℝ} (hx : 0 < x) : HasDerivAt pinskerH (pinskerG x) x := by
  have h2 : x + 2 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log x + 1) x :=
    hasDerivAt_mul_log hx.ne'
  have hid : HasDerivAt (fun y : ℝ => (5/2 : ℝ) * y) (5/2) x := by
    simpa using (hasDerivAt_id x).const_mul (5/2 : ℝ)
  have h4 : HasDerivAt (fun y : ℝ => (y+2)⁻¹) (-(1)/(x+2)^2) x :=
    ((hasDerivAt_id x).add_const 2).inv h2
  have h6 : HasDerivAt (fun y : ℝ => (27/2 : ℝ) * (y+2)⁻¹) ((27/2) * (-(1)/(x+2)^2)) x :=
    h4.const_mul (27/2 : ℝ)
  have h5 : HasDerivAt pinskerH (Real.log x + 1 - 5/2 + 7 * 0 - (27/2) * (-(1)/(x+2)^2)) x := by
    have := ((h1.sub hid).add_const 7).sub h6
    simpa [pinskerH] using this
  convert h5 using 1
  unfold pinskerG
  field_simp
  ring
