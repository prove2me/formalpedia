-- Prove2me | Theorems.Thm_GCDMoment_pairMoment_exceptional
-- name    : GCDMoment.pairMoment_exceptional
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:57:18.738959+00:00
-- url     : https://prove2.me/theorems/c6bd206c-2d48-4cd1-a2ec-4ec034c8b9ff
-- title:
--   The exceptional case `a = 2`: the spread inequality holds for every `k ≥ 3` as soon as the
-- statement:
--   The exceptional case `a = 2`: the spread inequality holds for every `k ≥ 3` as soon as the
--   base case does, with no condition relating `N` to `a+b+c+d`.
--
--   ```lean
--   theorem GCDMoment.pairMoment_exceptional{b c d : ℤ} (hc : 3 ≤ c) (hcd : c ≤ d) (hdb : d < b)
--       (hprod : 2 * b = c * d) (hbase : tailMoment 3 c d < b ^ 3) (m : ℕ) :
--       pairMoment (m + 3) c d < pairMoment (m + 3) 2 b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GCDMomentHigherInversion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GCDMomentHigherInversion.lean#L338

-- Thm stub generated from Novelty/GCDMomentHigherInversion.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentHigherInversion
import Definitions.Def_Novelty_GCDMomentPairInversion

/-!
# Every moment of order `k ≥ 3` identifies the factorisation

`Novelty.GCDMomentPairInversion` showed that the third moment is strictly monotone in the
spread of a factorisation, so it separates all nontrivial factorisations of a modulus, while
the second moment does not (`N = 28`, `N = 36`).  This file proves the *general* statement:
**for every `k ≥ 3` the `k`-th moment separates factorisations**, for *every* modulus: the
main argument covers all `N > 30`, and a separate induction disposes of the seven exceptional
quadruples below that.

The mechanism is a four-parameter factorisation of the moment difference.  Two coprime-shape
factorisations of the same modulus can always be written as

`a = g·α,  b = γ·δ,  c = g·γ,  d = α·δ`,  so `ab = cd = gαγδ = N`,

and then the difference of the two predicted moments factors completely:

`pairMoment (m+2) a b − pairMoment (m+2) c d = (γ−α)(δ−g)·[N·H_m·H'_m − H_{m+1}·H'_{m+1} − 1]`,

where `H_m = ∑_{i≤m} γ^i α^{m−i}` and `H'_m = ∑_{i≤m} δ^i g^{m−i}` are complete homogeneous
symmetric polynomials (`hSum`).  Since `H_{m+1} ≤ (γ+α)H_m` and `(γ+α)(δ+g) = a+b+c+d`, the
bracket is at least `H_m H'_m (N − (a+b+c+d)) − 1 ≥ 2·1·1 − 1 > 0` as soon as `m ≥ 1`
(i.e. `k ≥ 3`) and `N > a+b+c+d`; and `N > a+b+c+d` is automatic for `N > 30`
(`sum_lt_of_thirtyone_le`).

## Main results

* `sub_mul_hSum` — `(x−y)·H_m(x,y) = x^{m+1} − y^{m+1}`.
* `pairMoment_split_identity` — the four-parameter factorisation of the moment difference.
* `pairMoment_bracket_pos` — positivity of the bracket for `k ≥ 3` under `N > a+b+c+d`.
* `pairMoment_spread_strict_param` — strict monotonicity in the spread, parametrised form.
* `pairMoment_spread_strict` — **the coordinate-free statement**: for `k ≥ 3`, if
  `2 ≤ a < c ≤ d < b` and `ab = cd` with `a+b+c+d < ab`, then
  `pairMoment k c d < pairMoment k a b`.
* `sum_lt_of_thirtyone_le` — the side condition is automatic once `N ≥ 31`.
* `pairMoment_injective_of_three_le` — **every moment of order `k ≥ 3` separates all
  nontrivial factorisations of any modulus `N ≥ 31`.**
* `exceptional_quadruple_classification` — the side condition `a+b+c+d < ab` fails for exactly
  seven quadruples, all with `a = 2`.
* `tailMoment`, `tailMoment_step`, `tailMoment_lt_pow`, `pairMoment_exceptional` — a separate
  induction that handles those seven.
* `pairMoment_spread_strict_unconditional`, `pairMoment_injective_of_three_le_unconditional` —
  **the `N ≥ 31` hypothesis is removed: for every `k ≥ 3` and every modulus, the `k`-th moment
  separates all nontrivial factorisations.**
* `factorization_from_moment_oracle`, `factorization_from_any_moment` — **the oracle form**:
  for every `k ≥ 1`, the observed `k`-th gcd moment of a distinct-prime semiprime is matched by
  exactly one candidate factorisation, the true one.

Together with the `k = 2` collision law this settles the shape of the inversion problem: the
second moment is the *only* ambiguous member of the family, and no member is cheap.
-/

open GCDMoment

/-! ### Complete homogeneous sums -/









/-! ### The four-parameter factorisation of a moment difference -/




/-! ### The coordinate-free statement -/





/-! ### Removing the side condition: the seven exceptional quadruples

The hypothesis `a+b+c+d < ab` used above fails for exactly seven quadruples, all of them with
`a = 2` and `b = N/2`:

`(N;a,b,c,d) = (12;2,6,3,4), (16;2,8,4,4), (18;2,9,3,6), (20;2,10,4,5), (24;2,12,3,8),`
`(24;2,12,4,6), (30;2,15,3,10)`.

For each of them the *base* inequality `tailMoment 3 c d < b ^ 3` still holds (the tightest is
`215 < 216` for `(6;3,4)`), and a crude induction `tailMoment (k+1) c d ≤ d · tailMoment k c d`
with `d < b` propagates it to every `k ≥ 3`.  This removes the side condition entirely. -/

theorem GCDMoment.pairMoment_exceptional{b c d : ℤ} (hc : 3 ≤ c) (hcd : c ≤ d) (hdb : d < b)
    (hprod : 2 * b = c * d) (hbase : tailMoment 3 c d < b ^ 3) (m : ℕ) :
    pairMoment (m + 3) c d < pairMoment (m + 3) 2 b := by sorry
