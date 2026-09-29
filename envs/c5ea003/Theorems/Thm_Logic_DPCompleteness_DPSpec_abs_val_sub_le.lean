-- Prove2me | Theorems.Thm_Logic_DPCompleteness_DPSpec_abs_val_sub_le
-- name    : Logic.DPCompleteness.DPSpec.abs_val_sub_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:25:39.90486+00:00
-- url     : https://prove2.me/theorems/7d8d60f7-9b49-4352-95c4-54576e33330f
-- title:
--   Lipschitz stability of the DP optimum.
-- statement:
--   **Lipschitz stability of the DP optimum.** If two specifications differ by at most `a` on
--   the initial weights and at most `b` on every transition weight, then their value functions
--   differ by at most `a + n • b` at horizon `n`.
--
--   ```lean
--   theorem Logic.DPCompleteness.DPSpec.abs_val_sub_le{D D' : DPSpec S W} {a b : W}
--       (hinit : ∀ s, |D'.init s - D.init s| ≤ a) (hstep : ∀ i s t, |D'.step i s t - D.step i s t| ≤ b)
--       (n : ℕ) (s : S) : |D'.val n s - D.val n s| ≤ a + n • b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DPCompletenessStability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DPCompletenessStability.lean#L80

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

theorem Logic.DPCompleteness.DPSpec.abs_val_sub_le{D D' : DPSpec S W} {a b : W}
    (hinit : ∀ s, |D'.init s - D.init s| ≤ a) (hstep : ∀ i s t, |D'.step i s t - D.step i s t| ≤ b)
    (n : ℕ) (s : S) : |D'.val n s - D.val n s| ≤ a + n • b := by sorry
