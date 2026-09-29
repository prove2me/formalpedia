-- Prove2me | solution 1 for Singmaster.row_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:02:15.378986+00:00
-- url     : https://prove2.me/submissions/33652d0e-c0d0-4e77-813f-decf50e705b6

-- Sol generated from Combinatorics/SingmasterOccurrences.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
/-
# Singmaster's problem: how often can a number occur in Pascal's triangle?

Let `N(t) = #{(n,k) : k ≤ n and C(n,k) = t}` be the *multiplicity* of `t` in Pascal's
triangle.  Singmaster (1971) asked whether `N` is bounded on `t ≥ 2`; this is open.
This file develops the elementary structure theory that *is* provable:

* every occurrence of `t ≥ 2` lies in row `n ≤ t` (`Singmaster.row_le_of_choose_eq`),
  so `N(t)` is finite and is computed by the explicit `Finset` `Singmaster.occ t`;
* `N(2) = 1`, `N(3) = N(4) = N(5) = 2`, `N(6) = 3`, `N(10) = 4` (verified by decision
  procedure on the explicit finite search box);
* `N(t) ≥ 2` for every `t ≥ 3` (`Singmaster.two_le_mult`);
* `N(p) = 2` for every odd prime `p` (`Singmaster.mult_odd_prime`);
* `N(3003) ≥ 8` (`Singmaster.eight_le_mult_3003`);
* infinitely many `t` have `N(t) ≥ 4` (`Singmaster.four_le_mult_choose_two`);
* **an unconditional logarithmic upper bound** `N(t) ≤ 2 * Nat.log 2 t` for `t ≥ 2`
  (`Singmaster.mult_le_two_mul_log`).  This is the strongest general statement
  available by elementary means; Singmaster's conjecture asks to replace
  `2 * log₂ t` by an absolute constant.

The engine behind the upper bound is a cross-cutting pair of facts:
a *monotonicity* fact (for fixed `k ≥ 1`, `n ↦ C(n,k)` is strictly increasing, so each
column meets each value at most once) and a *growth* fact (`2^k ≤ C(n,k)` whenever
`2k ≤ n`, so only logarithmically many columns are relevant at all).
-/

open Finset

open Singmaster

/-! ## Elementary inequalities for binomial coefficients -/








/-! ## The occurrence set and the multiplicity function -/






/-! ## Small values -/







/- From here on `occ` is treated as an opaque finite set: all further reasoning goes
through `mem_occ_iff`, and this prevents the elaborator from trying to expand the
(astronomically large) search box for big values of `t`. -/

/-! ## Lower bounds -/




/-! ## Odd primes occur exactly twice -/



/-! ## An unconditional logarithmic upper bound

Singmaster's conjecture asserts `N(t) = O(1)`.  Unconditionally we can prove
`N(t) ≤ 2 log₂ t`, by combining column uniqueness with geometric growth. -/









open Singmaster in
theorem solution{n k : ℕ} (h1 : 1 ≤ k) (h2 : k + 1 ≤ n) : n ≤ n.choose k := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; simp [Nat.choose_one_right]
    rcases Nat.lt_or_ge (k + 1) n with hk | hk
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one]
      have h1' : p ≤ p.choose j := ih p (by omega) (by omega) (by omega)
      have h2' : p ≤ p.choose (j + 1) := ih p (by omega) (by omega) (by omega)
      omega
    · have hkn : k = n - 1 := by omega
      subst hkn
      have := Nat.choose_symm (n := n) (k := 1) (by omega)
      simp [Nat.choose_one_right] at this
      omega
