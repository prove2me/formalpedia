-- Prove2me | Definitions.Def_Logic_DPCompletenessWalks
-- name    : Logic_DPCompletenessWalks
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:53:25.656059+00:00
-- url     : https://prove2.me/theorems/e62eb6d0-c2e0-4677-ae31-047727e32f75
-- title:
--   Aether Catalog definitions — Logic_DPCompletenessWalks
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DPCompletenessWalks`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DPCompletenessWalks.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_DPCompleteness
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


namespace Logic.DPCompleteness

namespace DPSpec

variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]

/-- `walk D k m s t` is the optimal total weight of `m + 1` transitions leading from state `s`
at stage `k` to state `t` at stage `k + m + 1`.  (The `+ 1` shift avoids having to adjoin a
bottom element for empty walks.) -/
def walk (D : DPSpec S W) : ℕ → ℕ → S → S → W
  | k, 0, s, t => D.step k s t
  | k, (m + 1), s, t =>
      (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun u => D.step k s u + D.walk (k + 1) m u t)







end DPSpec

end Logic.DPCompleteness


