-- Prove2me | Definitions.Def_Logic_DPCompletenessStability
-- name    : Logic_DPCompletenessStability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:02.913606+00:00
-- url     : https://prove2.me/theorems/32bc9aa6-6cc1-4409-8aca-37d801902d6b
-- title:
--   Aether Catalog definitions — Logic_DPCompletenessStability
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DPCompletenessStability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DPCompletenessStability.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_DPCompleteness
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


namespace Logic.DPCompleteness

namespace DPSpec

section Shift

variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]

/-- Shift all initial weights by `a` and all transition weights by `b`. -/
def shift (D : DPSpec S W) (a b : W) : DPSpec S W :=
  ⟨fun s => D.init s + a, fun i s t => D.step i s t + b⟩




end Shift

section Stability

variable {S W : Type*} [AddCommGroup W] [Fintype S] [Nonempty S] [LinearOrder W]
  [IsOrderedAddMonoid W]







end Stability

end DPSpec

end Logic.DPCompleteness


