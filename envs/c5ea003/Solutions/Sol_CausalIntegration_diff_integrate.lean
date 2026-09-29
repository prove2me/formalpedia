-- Prove2me | solution 1 for CausalIntegration.diff_integrate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:22:40.023733+00:00
-- url     : https://prove2.me/submissions/c75a0ffb-30a1-4c7b-99ef-1e086df187d2

-- Sol generated from Combinatorics/CausalintegrationCore/CausalIntegration_Core.lean
import Mathlib
import Definitions.Def_Combinatorics_CausalintegrationCore_CausalIntegration_Core
import Theorems.Thm_CausalIntegration_integrate_succ

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






@[simp] lemma integrate_zero (f : Signal) : integrate f 0 = f 0 := by
  simp [integrate]


@[simp] lemma diff_zero (f : Signal) : diff f 0 = f 0 := by simp [diff]

lemma diff_succ (f : Signal) (n : ℕ) : diff f (n + 1) = f (n + 1) - f n := by
  simp [diff]





/-! ## The linear structure of causal operators -/






open CausalIntegration in
theorem solution(f : Signal) (n : ℕ) : diff (integrate f) n = f n := by
  rcases n with _ | m
  · simp
  · rw [diff_succ, integrate_succ]; ring
