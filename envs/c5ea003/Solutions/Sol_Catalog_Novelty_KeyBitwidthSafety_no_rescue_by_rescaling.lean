-- Prove2me | solution 1 for Catalog.Novelty.KeyBitwidthSafety.no_rescue_by_rescaling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:05:11.874039+00:00
-- url     : https://prove2.me/submissions/0bae6dd0-416e-4c98-a3b0-4eade579008a

-- Sol generated from Novelty/KeyBitwidthSafety.lean
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



open Catalog.Novelty.KeyBitwidthSafety in
theorem solution(c : ℝ) (hc : 0 < c) (q : Fin d → ℝ)
    (k : Fin (n + 1) → Fin d → ℝ) (R : ℝ) (b : ℕ) (hrange : ∀ i t, |k i t| ≤ R) :
    scores (fun t => q t / c) (fun i t => c * k i t) = scores q k ∧
      (∀ i t, |c * k i t| ≤ c * R) ∧
      (∑ t, |q t / c|) * res (c * R) b = (∑ t, |q t|) * res R b := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    simp only [scores]
    refine Finset.sum_congr rfl fun t _ => ?_
    field_simp
  · intro i t
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hrange i t) hc.le
  · have habs : ∀ t, |q t / c| = |q t| / c := by
      intro t
      rw [abs_div, abs_of_pos hc]
    simp only [habs, res, ← Finset.sum_div]
    field_simp
