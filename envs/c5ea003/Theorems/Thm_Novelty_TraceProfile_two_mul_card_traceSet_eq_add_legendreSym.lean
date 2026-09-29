-- Prove2me | Theorems.Thm_Novelty_TraceProfile_two_mul_card_traceSet_eq_add_legendreSym
-- name    : Novelty.TraceProfile.two_mul_card_traceSet_eq_add_legendreSym
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:18:11.505267+00:00
-- url     : https://prove2.me/theorems/96310e70-d434-460f-a214-7673d5c231d3
-- title:
--   The visible bit is the Legendre symbol.
-- statement:
--   **The visible bit is the Legendre symbol.**  The deviation of the trace-set size
--   from half the modulus is exactly `χ_q(N)`.  Since `χ_q(N)` is computable from `N`
--   alone (quadratic reciprocity), the single bit the trace reveals modulo `q` is public
--   data and gives no access to `p` or `q`.
--
--   ```lean
--   theorem Novelty.TraceProfile.two_mul_card_traceSet_eq_add_legendreSym(hq2 : q ≠ 2) (a : ℤ)
--       (ha : ((a : ZMod q)) ≠ 0) :
--       (2 * (traceSet ((a : ZMod q))).card : ℤ) = q + legendreSym q a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/TraceProfileCharacterArity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/TraceProfileCharacterArity.lean#L71

-- Thm stub generated from Novelty/TraceProfileCharacterArity.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileCharacterArity
import Definitions.Def_Novelty_TraceProfileTraceSet
/-
# TRACEPROFILE IV — what the visible bit *is*, and why it is an arity-2 phenomenon

Phase A research file (Novelty domain), Paper 50 / Experiment 385, second research
cycle.

Cycle I (`Novelty.TraceProfileTraceSet`) proved that the trace `s = p + q` of a
semiprime is pinned modulo an odd prime `q` to a set of size `(q + χ_q(N))/2` — one
bit per prime.  This file answers the two questions that cycle raised.

**Q1.  Which bit is it?**  `two_mul_card_traceSet_eq_add_legendreSym`: the deviation
of the trace-set size from `q/2` is *exactly* the Legendre symbol `χ_q(N)`.  So the
"one visible bit per prime" is the quadratic character of the public modulus — a
quantity computable from `N` alone in polynomial time (quadratic reciprocity).  It
is therefore public data, not a leak about `(p, q)`; this is the information-level
form of the paper's verdict "the trace is the least hidden invariant, but its
visible bits never isolate `p` or `q`".

**Q2.  Is the constraint special to two factors?**  Yes.  For three factors the
sum set `{x + y + z : x y z = N}` is *everything* already at `q = 11`
(`tripleSumSet_full_eleven`), while the two-factor trace set is always a proper
subset (`traceSet_ne_univ`).  Small primes `q ≤ 7` are exceptional
(`tripleSumSet_not_full_five`).  The trace constraint is an arity-2 phenomenon: it
is the quadratic discriminant, and nothing else.

## Main results

* `mem_traceSet_iff_isSquare_discrim` — the structural description of the trace set:
  `s` is a possible trace iff the discriminant `s² - 4N` is a square.
* `two_mul_card_traceSet_eq_add_legendreSym` — `2|S_q(N)| = q + χ_q(N)`.
* `card_traceSet_eq_of_legendreSym_eq` — the trace-set size sees `N` only through
  `χ_q(N)`: the whole visible bit is the (public) quadratic character.
* `odd_list_sum_prod_mod_four` — **the `k`-factor low-bit law**: for any list of odd
  numbers, `e₁ + 1 ≡ N + k (mod 4)` where `N` is the product and `k` the length.
  For `k = 2` this is the exact `s₁ = 1 - N₁` theorem of `TraceProfileLowBits`.
* `card_traceSet_le_card_tripleSumSet` — arity monotonicity.
* `tripleSumSet_full_eleven`, `tripleSumSet_not_full_five`, `traceSet_ne_univ` — the
  arity-2/arity-3 dichotomy, with the small-prime exceptions.
* `traceSet_injective_thirteen` — the trace set determines `N` (finite verification).
-/


open Novelty.TraceProfile

open Finset

/-! ## The structural description: the trace set is a discriminant condition -/


variable {q : ℕ} [hq : Fact (Nat.Prime q)]

theorem Novelty.TraceProfile.two_mul_card_traceSet_eq_add_legendreSym(hq2 : q ≠ 2) (a : ℤ)
    (ha : ((a : ZMod q)) ≠ 0) :
    (2 * (traceSet ((a : ZMod q))).card : ℤ) = q + legendreSym q a := by sorry
