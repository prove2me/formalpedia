-- Prove2me | Theorems.Thm_QubitTrade_truncOutcome_lt
-- name    : QubitTrade.truncOutcome_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:52:08.632567+00:00
-- url     : https://prove2.me/theorems/1d60735f-b3a9-4291-95b2-f16361a27c8d
-- title:
--   Outcomes live in the `t`-bit alphabet.
-- statement:
--   Outcomes live in the `t`-bit alphabet.
--
--   ```lean
--   theorem QubitTrade.truncOutcome_lt{t r k : ℕ} (hk : k < r) : truncOutcome t r k < 2 ^ t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/SupportCollapse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/SupportCollapse.lean#L42

-- Thm stub generated from Algebra/QubitTrade/SupportCollapse.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_Resolution
import Definitions.Def_Algebra_QubitTrade_SupportCollapse

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

open QubitTrade

theorem QubitTrade.truncOutcome_lt{t r k : ℕ} (hk : k < r) : truncOutcome t r k < 2 ^ t := by sorry
