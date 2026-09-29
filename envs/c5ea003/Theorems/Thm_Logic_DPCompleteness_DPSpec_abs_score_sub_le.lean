-- Prove2me | Theorems.Thm_Logic_DPCompleteness_DPSpec_abs_score_sub_le
-- name    : Logic.DPCompleteness.DPSpec.abs_score_sub_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:25:21.382254+00:00
-- url     : https://prove2.me/theorems/620a7bd4-a1ea-43da-8beb-8b4223cfc319
-- title:
--   Perturbation bound at the level of individual labelling scores.
-- statement:
--   Perturbation bound at the level of individual labelling scores.
--
--   ```lean
--   theorem Logic.DPCompleteness.DPSpec.abs_score_sub_le{D D' : DPSpec S W} {a b : W}
--       (hinit : ∀ s, |D'.init s - D.init s| ≤ a) (hstep : ∀ i s t, |D'.step i s t - D.step i s t| ≤ b)
--       (f : ℕ → S) : ∀ n : ℕ, |D'.score f n - D.score f n| ≤ a + n • b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DPCompletenessStability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DPCompletenessStability.lean#L99

-- Thm stub generated from Logic/DPCompletenessStability.lean
import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessStability
/-
# Stability of the DP value function under perturbation of the specification

The completeness theorem of `Logic.DPCompleteness` says the DP value is the exact optimum over
all labellings.  This file quantifies how that optimum reacts to perturbing the data.

* `DPSpec.shift` uniformly shifts the initial weights by `a` and every transition weight by `b`;
  `DPSpec.val_shift` shows the value function shifts by exactly `a + n • b` — the DP optimum is
  *equivariant* for the additive action of constants.
* `DPSpec.abs_val_sub_le` is the resulting Lipschitz stability bound: if two specifications
  differ by at most `a` on initial weights and at most `b` on transition weights, their value
  functions differ by at most `a + n • b` at horizon `n`.
* `DPSpec.near_optimal_transfer` turns this into a robustness statement about *runs*: a DP run
  computed for a perturbed model is within `2 • (a + n • b)` of the true optimum.  Combined with
  completeness this says the DP is not merely exact, but *stably* exact.

The weight monoid here is a linearly ordered additive commutative group (e.g. `ℤ`, `ℚ`, `ℝ`).
-/


open Logic.DPCompleteness

open DPSpec


variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]







variable {S W : Type*} [AddCommGroup W] [Fintype S] [Nonempty S] [LinearOrder W]
  [IsOrderedAddMonoid W]




omit [Fintype S] [Nonempty S] in

theorem Logic.DPCompleteness.DPSpec.abs_score_sub_le{D D' : DPSpec S W} {a b : W}
    (hinit : ∀ s, |D'.init s - D.init s| ≤ a) (hstep : ∀ i s t, |D'.step i s t - D.step i s t| ≤ b)
    (f : ℕ → S) : ∀ n : ℕ, |D'.score f n - D.score f n| ≤ a + n • b := by sorry
