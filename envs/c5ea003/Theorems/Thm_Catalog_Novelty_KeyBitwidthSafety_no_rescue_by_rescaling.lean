-- Prove2me | Theorems.Thm_Catalog_Novelty_KeyBitwidthSafety_no_rescue_by_rescaling
-- name    : Catalog.Novelty.KeyBitwidthSafety.no_rescue_by_rescaling
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:10:43.376314+00:00
-- url     : https://prove2.me/theorems/f601dfe2-147c-4c08-a40a-af7cf7b9b434
-- title:
--   No rescue by normalisation.
-- statement:
--   **No rescue by normalisation.**  Rescaling the keys by `c > 0` and the query
--   by `1/c` leaves the logits — hence the whole attention functional — unchanged,
--   multiplies the key range by `c`, and divides the query `ℓ¹` norm by `c`.  The
--   amplification `‖q‖₁ · R / 2^b` that governs `decision_preserved_of_key_bits` is
--   therefore *invariant*: no choice of scale, and hence no normalisation scheme,
--   can reduce the number of key bits required.  This is the sense in which the
--   NET-93 cliff is a property of attention rather than of one storage format.
--
--   ```lean
--   theorem Catalog.Novelty.KeyBitwidthSafety.no_rescue_by_rescaling(c : ℝ) (hc : 0 < c) (q : Fin d → ℝ)
--       (k : Fin (n + 1) → Fin d → ℝ) (R : ℝ) (b : ℕ) (hrange : ∀ i t, |k i t| ≤ R) :
--       scores (fun t => q t / c) (fun i t => c * k i t) = scores q k ∧
--         (∀ i t, |c * k i t| ≤ c * R) ∧
--         (∑ t, |q t / c|) * res (c * R) b = (∑ t, |q t|) * res R b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KeyBitwidthSafety.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KeyBitwidthSafety.lean#L108

-- Thm stub generated from Novelty/KeyBitwidthSafety.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation
import Definitions.Def_Novelty_KeyBitwidthSafety
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

open Catalog.Novelty.KeyBitwidthSafety

open Finset Catalog.Novelty.KeysOwnTheCliff Catalog.Novelty.KVDecisionDissociation

variable {n d : ℕ}







/-! ### Cycle 5: rescaling cannot buy key bits -/

theorem Catalog.Novelty.KeyBitwidthSafety.no_rescue_by_rescaling(c : ℝ) (hc : 0 < c) (q : Fin d → ℝ)
    (k : Fin (n + 1) → Fin d → ℝ) (R : ℝ) (b : ℕ) (hrange : ∀ i t, |k i t| ≤ R) :
    scores (fun t => q t / c) (fun i t => c * k i t) = scores q k ∧
      (∀ i t, |c * k i t| ≤ c * R) ∧
      (∑ t, |q t / c|) * res (c * R) b = (∑ t, |q t|) * res R b := by sorry
