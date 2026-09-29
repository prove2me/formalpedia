-- Prove2me | Theorems.Thm_Logic_DPCompleteness_DPSpec_val_add
-- name    : Logic.DPCompleteness.DPSpec.val_add
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:26:18.758779+00:00
-- url     : https://prove2.me/theorems/e2a4ba6f-43dc-47d2-a3be-ab18ecc2c466
-- title:
--   The forward value function is the max-plus action of the walk matrices on the value
-- statement:
--   The forward value function is the max-plus action of the walk matrices on the value
--   vector at an earlier stage.
--
--   ```lean
--   theorem Logic.DPCompleteness.DPSpec.val_add(D : DPSpec S W) :
--       ∀ (m k : ℕ) (t : S),
--         D.val (k + m + 1) t =
--           (Finset.univ : Finset S).sup' Finset.univ_nonempty
--             (fun s => D.val k s + D.walk k m s t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DPCompletenessWalks.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DPCompletenessWalks.lean#L93

-- Thm stub generated from Logic/DPCompletenessWalks.lean
import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessWalks
/-
# Walk algebra for layered dynamic programming

This file complements `Logic.DPCompleteness`. There the DP value function `val` and the
completeness theorem ("every labelling is dominated by some DP run") were established.
Here we develop the *segment* (walk) calculus that underlies the value function:

* `DPSpec.walk D k m s t` — the optimal weight of `m + 1` consecutive transitions starting
  in state `s` at stage `k` and ending in state `t` at stage `k + m + 1`;
* `DPSpec.walk_chapman_kolmogorov` — the max-plus Chapman–Kolmogorov identity, i.e.
  associativity of segment composition. In tropical language, this says that the family of
  matrices `walk D k m` forms a (shifted) semigroup under max-plus matrix multiplication;
* `DPSpec.val_add` — the forward value function is the max-plus action of the walk matrices
  on the initial value vector;
* `DPSpec.bval_eq_sup_walk` — the backward value function is the row-max of a walk matrix.

Finally we instantiate everything on an explicit three-state integer digraph and check the
computed values against a brute-force enumeration of all labellings, entirely inside Lean
using `decide`.
-/


open Logic.DPCompleteness

open DPSpec

variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]

theorem Logic.DPCompleteness.DPSpec.val_add(D : DPSpec S W) :
    ∀ (m k : ℕ) (t : S),
      D.val (k + m + 1) t =
        (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun s => D.val k s + D.walk k m s t) := by sorry
