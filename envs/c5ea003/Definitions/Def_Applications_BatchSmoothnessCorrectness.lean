-- Prove2me | Definitions.Def_Applications_BatchSmoothnessCorrectness
-- name    : Applications_BatchSmoothnessCorrectness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:32:04.867214+00:00
-- url     : https://prove2.me/theorems/616f3e23-405c-4de1-8880-809faa65d280
-- title:
--   Aether Catalog definitions — Applications_BatchSmoothnessCorrectness
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.BatchSmoothnessCorrectness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/BatchSmoothnessCorrectness.lean by skeleton subtraction
import Mathlib

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

namespace BatchSmoothness

open Finset

/-! ## The batch modulus -/

/-- `primorialUpTo B` is the product of all primes `≤ B`; the modulus at the
root of the product tree of the factor base. -/
def primorialUpTo (B : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow (B + 1), p





/-! ## Smoothness -/

/-- `n` is `B`-smooth: all of its prime factors are at most `B`.  This is the
predicate that solo trial division against the factor base decides. -/
def IsSmooth (B n : ℕ) : Prop := ∀ p, p.Prime → p ∣ n → p ≤ B


/-! ## The batch criterion is exactly smoothness -/






/-! ## Tree shape is irrelevant (the "tree vs direct" arm of the audit) -/

/-- A binary product tree over a list of leaves. -/
inductive ProdTree : Type
  | leaf : ℕ → ProdTree
  | node : ProdTree → ProdTree → ProdTree
  deriving Repr

namespace ProdTree

/-- The value computed at the root: multiply children bottom-up. -/
def eval : ProdTree → ℕ
  | leaf n => n
  | node l r => l.eval * r.eval

/-- The leaves, left to right. -/
def leaves : ProdTree → List ℕ
  | leaf n => [n]
  | node l r => l.leaves ++ r.leaves



end ProdTree

/-! ## The audit, as a theorem -/



end BatchSmoothness


