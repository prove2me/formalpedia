-- Prove2me | Definitions.Def_Algebra_QubitTrade_SupportCollapse
-- name    : Algebra_QubitTrade_SupportCollapse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:54:38.233917+00:00
-- url     : https://prove2.me/theorems/84286f30-6fdd-4b41-b5d9-99a8196170b7
-- title:
--   Aether Catalog definitions — Algebra_QubitTrade_SupportCollapse
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QubitTrade.SupportCollapse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QubitTrade/SupportCollapse.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution

/-!
# QUBIT-TRADE II: classical collapse of a truncated register

A `t`-bit truncated phase register reports, for an order-`r` Shor sample with
numerator `k`, the integer

  `truncOutcome t r k = ⌊2^t · k / r⌋ = (2^t * k) / r`  (natural division).

This file proves the **collapse** half of the experiment: once `2^t ≤ r`, the
outcome map is *onto* the whole outcome alphabet `{0, …, 2^t - 1}`, so the set of
observable records is `{0, …, 2^t-1}` **independently of `r`**.  Consequently:

* `QubitTrade.truncOutcome_surjective` — surjectivity onto the alphabet;
* `QubitTrade.outcomes_eq_alphabet` — the outcome set does not depend on `r`;
* `QubitTrade.outcome_lists_coincide` — every *record* (list of samples, of any
  length) achievable at order `r` is achievable at order `r'`;
* `QubitTrade.samples_do_not_help` — hence **no** estimator, with **any** number
  of samples, can be correct for two distinct orders `r, r' ≥ 2^t`;
* `QubitTrade.collapse_cardinality` — the collapse is massive: all
  `R - 2^t + 1` orders in `[2^t, R]` share one and the same outcome set.

This is the sample-independent lower bound `t > log₂ r`.  It is strictly weaker
than the resolution threshold `t ≈ 2 log₂ r` of `Resolution.lean`, and the two
together bracket the measured `t_min`.
-/

namespace QubitTrade

/-- The outcome of a `t`-bit truncated register on the exact phase `k / r`. -/
def truncOutcome (t r k : ℕ) : ℕ := 2 ^ t * k / r




/-- The set of records a `t`-bit register can produce at order `r`. -/
def outcomes (t r : ℕ) : Set ℕ := {m | ∃ k < r, truncOutcome t r k = m}








end QubitTrade


