-- Prove2me | Definitions.Def_Novelty_KeyBitwidthSafety
-- name    : Novelty_KeyBitwidthSafety
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:30:08.918998+00:00
-- url     : https://prove2.me/theorems/20863843-0b70-4c06-b6b5-164da4759aaf
-- title:
--   Aether Catalog definitions — Novelty_KeyBitwidthSafety
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KeyBitwidthSafety`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KeyBitwidthSafety.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation
import Definitions.Def_Novelty_KeysOwnTheCliff

/-!
# How many bits do the keys need?  A margin criterion and a 4-bit counterexample

Cycle 4 of the NET-93 thread.  `Novelty.KeysOwnTheCliff` proves that the key
path has no Lipschitz constant, and `Novelty.KVBitBudgetSplit` proves that bits
should be moved from the values to the keys.  Neither answers the deployment
question NET-93 actually poses: *how many* key bits are enough?

This file answers it with the margin certificate of
`Novelty.KVDecisionDissociation` (`strictTop_of_margin`: a top-1 decision
survives a coordinatewise `ε`-perturbation of the logits whenever its gap
exceeds `2ε`).  Composing that certificate with the key-amplification bound
`score_error_le_of_key_error` gives:

* `decision_preserved_of_key_bits` — a `b`-bit key grid of range `R` preserves
  every attention decision whose logit margin exceeds `2 · ‖q‖₁ · R / 2^b`;
* `bits_suffice_for_margin` — hence `2^b > 2‖q‖₁R/m` bits are enough for all
  decisions of margin at least `m`.  The requirement is *logarithmic* in the
  amplification `‖q‖₁R/m`, which is why 8 bits is a plausible frontier and 4 is
  not: each bit doubles the tolerated amplification;
* `eight_bits_safe_at_scale` — at the reference scale `‖q‖₁ = 64`, `R = 1`,
  `m = 1`, eight bits leave a factor-two safety margin;
* `four_bits_destroy_the_decision` — and at the *same* scale four bits provably
  destroy a decision of margin `2`: the exact scores have a strict top-1, the
  quantised ones tie.  A single collapsed decision is exactly the mechanism by
  which the measured `K q4_0` arm reaches PPL 2537.

Both halves are constructive and quantitative, so the pair brackets the NET-93
deployment rule "keys ≥ 8 bits, values may take 4".
-/

namespace Catalog.Novelty.KeyBitwidthSafety

open Finset Catalog.Novelty.KeysOwnTheCliff Catalog.Novelty.KVDecisionDissociation

variable {n d : ℕ}

/-- Resolution of a uniform `b`-bit grid covering the key range `[-R, R]`
(worst-case rounding error per entry). -/
noncomputable def res (R : ℝ) (b : ℕ) : ℝ := R / 2 ^ b






/-! ### Cycle 5: rescaling cannot buy key bits -/


end Catalog.Novelty.KeyBitwidthSafety


