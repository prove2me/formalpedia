-- Prove2me | Theorems.Thm_Logic_DPCompleteness_DPSpec_exists_backtrace_ending
-- name    : Logic.DPCompleteness.DPSpec.exists_backtrace_ending
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:26:50.650875+00:00
-- url     : https://prove2.me/theorems/11a2e3f2-6bc2-4cd6-b2b3-7e689ad05d1f
-- title:
--   Realisability without cancellativity.
-- statement:
--   **Realisability without cancellativity.** Every DP value is attained by a backtrace.
--
--   ```lean
--   theorem Logic.DPCompleteness.DPSpec.exists_backtrace_ending(D : DPSpec S W) :
--       ∀ (n : ℕ) (s : S), ∃ f : ℕ → S, f n = s ∧ D.IsBacktrace n f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DPCompletenessConstrained.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DPCompletenessConstrained.lean#L63

-- Thm stub generated from Logic/DPCompletenessConstrained.lean
import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessConstrained
/-
# Completeness without cancellativity, and constrained dynamic programming

In `Logic.DPCompleteness` the notion `IsDPRun` was *semantic* (all prefix scores are optimal)
and the existence of runs was proved using cancellativity of the weight monoid.  This file
removes that hypothesis by working with the *structural* (backtrace) notion of a run:

> `IsBacktrace D n f` : at each stage the DP recursion is realised on the nose,
> `val i (f i) + step i (f i) (f (i+1)) = val (i+1) (f (i+1))`.

The two notions turn out to be equivalent for **every** ordered weight monoid
(`isBacktrace_iff_isDPRun`), and completeness holds with no cancellativity assumption
(`dp_complete_general`).  This is exactly what is needed to cover **constrained** dynamic
programming, where infeasible transitions carry the absorbing weight `⊥` of `WithBot W` — a
monoid that is emphatically *not* cancellative.

As an application we characterise infeasibility (`val_eq_bot_iff`) and instantiate the theory on
the classical maximum-weight independent set problem on a path.
-/


open Logic.DPCompleteness

open DPSpec

/-! ## Structural runs -/


variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]




omit [AddLeftMono W] in

theorem Logic.DPCompleteness.DPSpec.exists_backtrace_ending(D : DPSpec S W) :
    ∀ (n : ℕ) (s : S), ∃ f : ℕ → S, f n = s ∧ D.IsBacktrace n f := by sorry
