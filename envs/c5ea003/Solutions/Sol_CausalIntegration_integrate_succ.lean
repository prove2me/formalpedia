-- Prove2me | solution 1 for CausalIntegration.integrate_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:20:23.481295+00:00
-- url     : https://prove2.me/submissions/3c14aa88-d8ec-4c6f-9ebd-635fce6c8645

-- Sol generated from Combinatorics/CausalintegrationCore/CausalIntegration_Core.lean
import Mathlib
import Definitions.Def_Combinatorics_CausalintegrationCore_CausalIntegration_Core

/-!
# Causal integration: core

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/CausalIntegration/Core.lean`.  It is reconstructed here
as a self-contained development of *discrete causal operators*.

An operator `T` on discrete signals `ℕ → ℝ` is **causal** when the value of `T f`
at time `n` depends only on the samples `f 0, …, f n`.  The prototypical causal
operator is discrete integration (running sum), and its (formal) inverse is the
backward difference.  The main results here are:

* `CausalIntegration.integrate_isCausal` — the running sum is causal;
* `CausalIntegration.integrate_diff` and `CausalIntegration.diff_integrate` — the
  **discrete fundamental theorem of calculus**: difference and integration are
  mutually inverse;
* `CausalIntegration.isCausal_id`, `isCausal_add`, `isCausal_smul` — the causal
  operators form a submodule of all operators.
-/

open CausalIntegration














/-! ## The linear structure of causal operators -/






open CausalIntegration in
theorem solution(f : Signal) (n : ℕ) :
    integrate f (n + 1) = integrate f n + f (n + 1) := by
  simp [integrate, Finset.sum_range_succ]
