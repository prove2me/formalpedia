-- Prove2me | Theorems.Thm_Singmaster_choose_eq_iff_descFactorial
-- name    : Singmaster.choose_eq_iff_descFactorial
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:31:14.50425+00:00
-- url     : https://prove2.me/theorems/c908a2e4-5f77-4cad-9ffd-d6d743c036b5
-- title:
--   `C(n,k) = t` is equivalent to `n^{\underline{k}} = k!
-- statement:
--   `C(n,k) = t` is equivalent to `n^{\underline{k}} = k! · t`.  This is the form in
--   which the finite searches below are executed: the descending factorial is a product of
--   `k` factors, whereas evaluating `Nat.choose` by its defining recursion costs about
--   `C(n,k)` additions.
--
--   ```lean
--   theorem Singmaster.choose_eq_iff_descFactorial{n k t : ℕ} :
--       n.choose k = t ↔ n.descFactorial k = Nat.factorial k * t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterExactCounts.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterExactCounts.lean#L44

-- Thm stub generated from Combinatorics/SingmasterExactCounts.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterOccurrences
/-
# Exact multiplicities: a certified finite algorithm, and `N(3003) = 8`

Fifth research cycle.  The earlier files bound or reduce the multiplicity function
`N(t) = Singmaster.mult t`; this file turns the structure theory into a *certified
decision procedure* for a single value of `t`, and runs it.

## The algorithm

Every occurrence of `t ≥ 3` is either one of the two boundary occurrences `(t,1)`,
`(t,t-1)`, or an **interior** one, i.e. `C(n,k) = t` with `2 ≤ k ≤ n - 2`.  An interior
occurrence satisfies `C(n,2) ≤ C(n,k) = t` (`Singmaster.choose_two_le_choose`), so its
row is capped by any `N` with `t < C(N,2)`; that is, by roughly `√(2t)`.  Hence

`N(t) = 2 + #{(n,k) : n,k < N, 2 ≤ k ≤ n-2, C(n,k) = t}`,

a search over an explicitly bounded box (`Singmaster.mult_eq_two_add_interior`).  As in
`Combinatorics.SingmasterCentralBinomial` the test `C(n,k) = t` is carried out through
`Nat.descFactorial` (`Singmaster.choose_eq_iff_descFactorial`), which costs `k`
multiplications instead of `C(n,k)` additions and is what makes kernel evaluation
possible.

## Results

* `Singmaster.mult_eq_two_add_interior` — the certified algorithm;
* `Singmaster.mult_eq_two_of_no_interior` — the "only the two trivial occurrences" case;
* `Singmaster.mult_3003` — **`3003` occurs exactly eight times**, upgrading
  `Singmaster.eight_le_mult_3003` from a lower bound to an equality.  This is the
  specimen singled out in Singmaster's problem;
* `Singmaster.mult_120`, `mult_210`, `mult_1540`, `mult_7140`, `mult_11628` — the other
  small numbers of multiplicity six: each occurs **exactly** six times.

Together with `Combinatorics.SingmasterCentralBinomial` this makes every multiplicity
claim in the classical folklore list machine-checked, except for the asymptotic ones.
-/

open Finset

open Singmaster

/-! ## Binomial coefficients through descending factorials -/

theorem Singmaster.choose_eq_iff_descFactorial{n k t : ℕ} :
    n.choose k = t ↔ n.descFactorial k = Nat.factorial k * t := by sorry
