-- Prove2me | Definitions.Def_Combinatorics_CausalintegrationCore_CausalIntegration_Core
-- name    : Combinatorics_CausalintegrationCore_CausalIntegration_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:29:15.309042+00:00
-- url     : https://prove2.me/theorems/801be6f7-58ae-49b1-a159-82c5b4daeef3
-- title:
--   Aether Catalog definitions — Combinatorics_CausalintegrationCore_CausalIntegration_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.CausalintegrationCore.CausalIntegration.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/CausalintegrationCore/CausalIntegration_Core.lean by skeleton subtraction
import Mathlib

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

namespace CausalIntegration

/-- A discrete signal. -/
abbrev Signal : Type := ℕ → ℝ

/-- An operator on signals. -/
abbrev Op : Type := Signal → Signal

/-- `T` is **causal** if `T f n` only depends on the values `f k` for `k ≤ n`. -/
def IsCausal (T : Op) : Prop :=
  ∀ f g : Signal, ∀ n : ℕ, (∀ k, k ≤ n → f k = g k) → T f n = T g n

/-- Discrete integration: the running sum `(∫ f)(n) = ∑_{k ≤ n} f k`. -/
def integrate (f : Signal) : Signal := fun n => ∑ k ∈ Finset.range (n + 1), f k

/-- Backward difference, with the convention `(Δ f)(0) = f 0`. -/
def diff (f : Signal) : Signal := fun n => if n = 0 then f 0 else f n - f (n - 1)









/-! ## The linear structure of causal operators -/





end CausalIntegration


