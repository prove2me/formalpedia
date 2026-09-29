-- Prove2me | Definitions.Def_Combinatorics_SingmasterExactCounts
-- name    : Combinatorics_SingmasterExactCounts
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:53:20.678397+00:00
-- url     : https://prove2.me/theorems/9903e09a-e0d7-4525-b550-e593d1688993
-- title:
--   Aether Catalog definitions — Combinatorics_SingmasterExactCounts
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.SingmasterExactCounts`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/SingmasterExactCounts.lean by skeleton subtraction
import Mathlib
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

namespace Singmaster

/-! ## Binomial coefficients through descending factorials -/


/-! ## The interior occurrences -/

/-- The interior occurrences of `t` inside the box `[0,N) × [0,N)`: positions `(n,k)`
with `2 ≤ k ≤ n - 2` and `C(n,k) = t`. -/
def interiorOcc (t N : ℕ) : Finset (ℕ × ℕ) :=
  ((range N) ×ˢ (range N)).filter
    (fun p => 2 ≤ p.2 ∧ p.2 + 2 ≤ p.1 ∧ p.1.descFactorial p.2 = Nat.factorial p.2 * t)


/-! ## The certified algorithm -/



/-! ## Running the algorithm

Each of the following is an honest finite search: for `t = 3003` the box is
`79 × 79` and the six interior occurrences found are `(78,2)`, `(78,76)`, `(15,5)`,
`(15,10)`, `(14,6)`, `(14,8)`. -/








end Singmaster


