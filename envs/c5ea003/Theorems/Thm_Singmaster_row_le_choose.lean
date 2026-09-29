-- Prove2me | Theorems.Thm_Singmaster_row_le_choose
-- name    : Singmaster.row_le_choose
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:30:32.136793+00:00
-- url     : https://prove2.me/theorems/0d24050e-d8d4-49f9-9aa0-645438ee2423
-- title:
--   Every interior entry of row `n` is at least `n`.
-- statement:
--   Every interior entry of row `n` is at least `n`.
--
--   ```lean
--   theorem Singmaster.row_le_choose{n k : ℕ} (h1 : 1 ≤ k) (h2 : k + 1 ≤ n) : n ≤ n.choose k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterOccurrences.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterOccurrences.lean#L62

-- Thm stub generated from Combinatorics/SingmasterOccurrences.lean
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

theorem Singmaster.row_le_choose{n k : ℕ} (h1 : 1 ≤ k) (h2 : k + 1 ≤ n) : n ≤ n.choose k := by sorry
