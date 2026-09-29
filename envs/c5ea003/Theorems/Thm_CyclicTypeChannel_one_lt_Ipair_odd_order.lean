-- Prove2me | Theorems.Thm_CyclicTypeChannel_one_lt_Ipair_odd_order
-- name    : CyclicTypeChannel.one_lt_Ipair_odd_order
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:30:15.938987+00:00
-- url     : https://prove2.me/theorems/62f5c12d-b53f-4459-84ce-a80965b5f457
-- title:
--   An odd cyclic order strictly above the one-bit binary-fork cap.
-- statement:
--   **An odd cyclic order strictly above the one-bit binary-fork cap.**
--
--   `M = 9 Â· 5 Â· 7 Â· 11 Â· 13 Â· 17 Â· 19 Â· 23 Â· 29 Â· 31 = 300840735195`
--   is odd and satisfies `Ipair M > 1`.  Together with `odd_orders_below_cap` (all
--   small odd orders are below the cap) this shows the cap is broken by accumulating
--   enough odd primary parts, not by the presence of an order-two element.
--
--   ```lean
--   theorem CyclicTypeChannel.one_lt_Ipair_odd_order: 1 < Ipair 300840735195 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelOdd.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelOdd.lean#L213

-- Thm stub generated from Shared/CyclicTypeChannelOdd.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
/-
# Odd cyclic orders above the one-bit cap

The exact-value files show the type-pair channel `Ipair n` breaking the one-bit
binary-fork cap at `n = 4, 6, 8, 10, 12, 16`, and staying below it at the odd
orders `3, 5, 9, 15` (`odd_orders_below_cap`).  That coincidence suggested that
the order-two element of the cyclic group is what pushes the channel above the
cap.  This file **refutes** that reading:

`one_lt_Ipair_odd_order` exhibits an explicit **odd** cyclic order

  `M = 9 · 5 · 7 · 11 · 13 · 17 · 19 · 23 · 29 · 31 = 300840735195`

with `1 < Ipair M`.  So the cap is broken by odd orders too; evenness is not the
mechanism.  What *is* the mechanism is CRT additivity (`Ipair_mul_of_coprime`)
together with the fact that every prime-order channel is strictly positive: the
channel of a squarefree-ish odd order is a *sum* of small positive prime
contributions.  The accumulation is *tight*: the prime-order values decay like
`Ipair p ≈ (log₂ p + 2/ln 2)/p²`, so the total over all odd prime powers
converges (numerically to `≈ 1.084`), and the ten primary parts used here
already give `1.0052…` — no odd order can exceed `1.09`, and only a long tail of
primes gets past `1` at all.

The proof is a chain of three ingredients, all already formal:

* `Ipair_prime` — the closed form for a prime cyclic order;
* `Ipair_val_9` — the exact value of the prime-power order `9`;
* `Ipair_mul_of_coprime` — CRT additivity.

Each prime contribution is bounded below by an explicit rational number obtained
from integer inequalities `2 ^ a ≤ x ^ 4096` and `x ^ 4096 ≤ 2 ^ c`
(`logb_ge_of_pow_le`, `logb_le_of_le_pow`); summing the ten bounds gives
`Ipair M ≥ 1.0052… > 1`.
-/

open CyclicTypeChannel

set_option exponentiation.threshold 100000

/-! ## 1. Rational bounds for binary logarithms -/



/-! ## 2. Explicit rational lower bounds for the odd prime-order channels

Each bound is the closed form `Ipair_prime` evaluated with the two-sided
rational bounds of Section 1 at denominator `4096`. -/











/-! ## 3. An odd cyclic order above the one-bit cap -/

theorem CyclicTypeChannel.one_lt_Ipair_odd_order: 1 < Ipair 300840735195 := by sorry
