-- Prove2me | solution 1 for NeuroSymbolicRLHF.hasDerivAt_pinskerG
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:26:00.769915+00:00
-- url     : https://prove2.me/submissions/803d70d9-22f1-4335-9457-065d56b233dd

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
theorem solution{x : ℝ} (hx : 0 < x) :
    HasDerivAt pinskerG (1/x - 27/(x+2)^3) x := by
  have h2 : x + 2 ≠ 0 := by linarith
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h3 : HasDerivAt (fun y : ℝ => (y+2)^2) (2*(x+2)) x := by
    have := ((hasDerivAt_id x).add_const 2).pow 2
    simpa using this
  have h4 : HasDerivAt (fun y : ℝ => ((y+2)^2)⁻¹) (-(2*(x+2))/((x+2)^2)^2) x :=
    h3.inv (by positivity)
  have h6 : HasDerivAt (fun y : ℝ => (27/2 : ℝ) * ((y+2)^2)⁻¹)
      ((27/2) * (-(2*(x+2))/((x+2)^2)^2)) x := h4.const_mul (27/2 : ℝ)
  have h5 : HasDerivAt pinskerG (x⁻¹ + 0 - 0 + (27/2) * (-(2*(x+2))/((x+2)^2)^2)) x := by
    have := ((h1.add_const 1).sub_const (5/2 : ℝ)).add h6
    simpa [pinskerG] using this
  convert h5 using 1
  field_simp
  ring
