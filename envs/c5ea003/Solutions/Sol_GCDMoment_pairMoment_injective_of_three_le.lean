-- Prove2me | solution 1 for GCDMoment.pairMoment_injective_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:45:01.751007+00:00
-- url     : https://prove2.me/submissions/eff98dad-5f90-49d2-bb7a-605bb808a30c

-- Sol generated from Novelty/GCDMomentHigherInversion.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentHigherInversion
import Definitions.Def_Novelty_GCDMomentPairInversion
import Theorems.Thm_GCDMoment_pairMoment_spread_strict

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



/-- For `N ≥ 31` the side condition `a+b+c+d < N` is automatic. -/
theorem sum_lt_of_thirtyone_le {a b c d : ℕ} (ha : 2 ≤ a) (hac : a < c) (hcd : c ≤ d)
    (hab : a ≤ b) (hprod : a * b = c * d) (hN : 31 ≤ a * b) : a + b + c + d < a * b := by
  have hc3 : 3 ≤ c := by omega
  have h1 : 2 * (a + b) ≤ 4 + a * b := by nlinarith [Nat.sub_add_cancel ha]
  have h2 : 3 * (c + d) ≤ 9 + c * d := by nlinarith
  have h3 : c * d = a * b := hprod.symm
  omega


/-! ### Removing the side condition: the seven exceptional quadruples

The hypothesis `a+b+c+d < ab` used above fails for exactly seven quadruples, all of them with
`a = 2` and `b = N/2`:

`(N;a,b,c,d) = (12;2,6,3,4), (16;2,8,4,4), (18;2,9,3,6), (20;2,10,4,5), (24;2,12,3,8),`
`(24;2,12,4,6), (30;2,15,3,10)`.

For each of them the *base* inequality `tailMoment 3 c d < b ^ 3` still holds (the tightest is
`215 < 216` for `(6;3,4)`), and a crude induction `tailMoment (k+1) c d ≤ d · tailMoment k c d`
with `d < b` propagates it to every `k ≥ 3`.  This removes the side condition entirely. -/









/-! ### The oracle corollary: any `k ≥ 3` moment factors the modulus -/



/-- Sanity check on the tightest small instance, `36 = 4·9 = 6·6`. -/
example : pairMoment 3 6 6 < pairMoment 3 4 9 := by norm_num [pairMoment]
example : pairMoment 5 6 6 < pairMoment 5 4 9 := by norm_num [pairMoment]


open GCDMoment in
theorem solution{a b c d : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 2 ≤ c)
    (hcd : c ≤ d) (hprod : a * b = c * d) (hN : 31 ≤ a * b) (m : ℕ)
    (hm : pairMoment (m + 3) (a : ℤ) (b : ℤ) = pairMoment (m + 3) (c : ℤ) (d : ℤ)) :
    a = c ∧ b = d := by
  have hac : a = c := by
    rcases lt_trichotomy a c with hlt | heq | hgt
    · have hdb : d < b := by nlinarith
      have hsum := sum_lt_of_thirtyone_le ha hlt hcd hab hprod hN
      exact absurd hm (by have := pairMoment_spread_strict ha hlt hcd hdb hprod hsum m; linarith)
    · exact heq
    · have hbd : b < d := by nlinarith
      have hsum := sum_lt_of_thirtyone_le hc hgt hab hcd hprod.symm (by omega)
      exact absurd hm.symm
        (by have := pairMoment_spread_strict hc hgt hab hbd hprod.symm hsum m; linarith)
  refine ⟨hac, ?_⟩
  have ha0 : 0 < a := by omega
  have : a * b = a * d := by rw [hprod, hac]
  exact Nat.eq_of_mul_eq_mul_left ha0 this
