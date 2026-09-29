-- Prove2me | Theorems.Thm_BatchSmoothness_criterion_fails_without_size_bound
-- name    : BatchSmoothness.criterion_fails_without_size_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:00.355136+00:00
-- url     : https://prove2.me/theorems/c9ec8025-c1c1-4cc2-93fc-193ed6a3b42f
-- title:
--   The completeness direction genuinely needs the size bound: with `t = 1`
-- statement:
--   The completeness direction genuinely needs the size bound: with `t = 1`
--   the smooth number `4` fails the criterion for every bound `B`.
--
--   ```lean
--   theorem BatchSmoothness.criterion_fails_without_size_bound(B : ℕ) (hB : 2 ≤ B) :
--       IsSmooth B 4 ∧ ¬ (4 ∣ (primorialUpTo B) ^ 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BatchSmoothnessCorrectness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BatchSmoothnessCorrectness.lean#L161

-- Thm stub generated from Applications/BatchSmoothnessCorrectness.lean
import Mathlib
import Definitions.Def_Applications_BatchSmoothnessCorrectness

/-!
# Exactness of product-tree batch smoothness testing

Experiment 561 ("BATCH-WINS-TESTING") compared *product-tree batch smoothness
testing* against *solo trial division* on pools of `k ∈ {1, 8, 64, 512}`
candidates with smoothness bound `B = 100` and candidates of bit length `40`.
Alongside the cost measurement (formalised in
`Catalog/Applications/BatchSmoothnessCost.lean`) the experiment ran an
**exact-match audit**: the smooth set reported by the batch algorithm agreed
with per-item trial division on 500/500 samples, in all three variants
(tree-vs-trial, direct-vs-trial, vector).

This file replaces that finite audit by a theorem: the batch criterion and
trial division agree on *every* input in the tested range, not merely on 500
samples.

## The algorithm being modelled

Let `P = ∏ {p prime : p ≤ B}` (`primorialUpTo B`).  Bernstein's batch test
computes, for each candidate `n`, the residue `P mod n` in a remainder tree and
then squares it `e` times modulo `n`; it declares `n` smooth exactly when the
result is `0 mod n`, i.e. exactly when `n ∣ P ^ (2 ^ e)`.

## Main results

* `smooth_iff_dvd_primorial_pow` — the exponent criterion:
  for `0 < n < 2 ^ t`, `n` is `B`-smooth **iff** `n ∣ P ^ t`.
  (Both directions are needed: `←` is soundness, `→` is completeness, and
  completeness is exactly where the bit-length bound `n < 2 ^ t` enters.)
* `smooth_iff_dvd_primorial_pow_two_pow` — the repeated-squaring form actually
  implemented: any `e` with `t ≤ 2 ^ e` works.
* `smooth_iff_mod_criterion` — the criterion survives the modular reduction
  performed by the remainder tree.
* `exponent_sharp` — the bit-length bound is sharp: `2 ^ t ∤ P ^ s` for `s < t`,
  so no smaller exponent can be used.
* `ProdTree.eval_eq_leaves_prod` and `ProdTree.eval_eq_primorial` — the value of
  a product tree is independent of its shape, which is why the "tree" and
  "direct" arms of the audit cannot disagree.
* `batch_filter_eq_trial_filter` — the audit statement itself: on any finite
  pool of candidates below `2 ^ t`, the batch-detected smooth set **equals** the
  trial-division smooth set.
* `batch_audit_500` — a machine-checked instance of the audit on the pool
  `{1, …, 500}` with `B = 100`.
-/

open BatchSmoothness

open Finset

/-! ## The batch modulus -/






/-! ## Smoothness -/



/-! ## The batch criterion is exactly smoothness -/

theorem BatchSmoothness.criterion_fails_without_size_bound(B : ℕ) (hB : 2 ≤ B) :
    IsSmooth B 4 ∧ ¬ (4 ∣ (primorialUpTo B) ^ 1) := by sorry
