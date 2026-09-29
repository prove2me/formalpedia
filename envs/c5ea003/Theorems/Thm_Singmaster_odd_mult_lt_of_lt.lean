-- Prove2me | Theorems.Thm_Singmaster_odd_mult_lt_of_lt
-- name    : Singmaster.odd_mult_lt_of_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:34:18.687194+00:00
-- url     : https://prove2.me/theorems/d65e2ba6-0510-49fc-aa1a-b0f2fede195e
-- title:
--   Every `t ≥ 2` below `C(22,11) = 705432` whose multiplicity is odd is one of
-- statement:
--   Every `t ≥ 2` below `C(22,11) = 705432` whose multiplicity is odd is one of
--   `2, 6, 20, 70, 252, 924, 3432, 12870, 48620, 184756`, and its multiplicity is `1`
--   (only for `t = 2`) or `3`.
--
--   ```lean
--   theorem Singmaster.odd_mult_lt_of_lt{t : ℕ} (ht : 2 ≤ t) (hlt : t < 705432) (hodd : Odd (mult t)) :
--       mult t = 1 ∨ mult t = 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterCentralBinomial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterCentralBinomial.lean#L290

-- Thm stub generated from Combinatorics/SingmasterCentralBinomial.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomial
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
/-
# Central binomial coefficients occur exactly three times (verified initial segment)

Fourth research cycle, building on

* `Combinatorics.SingmasterOccurrences` (the occurrence set `occ`, the multiplicity
  `mult`, monotonicity and growth of binomial coefficients),
* `Combinatorics.SingmasterRefinements` (strict unimodality of a row),
* `Combinatorics.SingmasterParity` (the parity criterion: `N(t)` is odd iff `t` is a
  central binomial coefficient).

The parity criterion reduced the open question "does any number occur exactly five or
exactly seven times?" to the single sequence `C(2m,m) = 2, 6, 20, 70, 252, 924, …`.
This file makes that reduction *effective* and then executes it for `m ≤ 10`.

## The effective criterion

For `t = C(2m,m)` with `m ≥ 2` we prove a **sandwich theorem**
(`Singmaster.choose_lt_centralBinom`): every entry `C(n,k)` with `n ≤ 2m` other than
the central entry itself is *strictly smaller* than `t`.  Hence any further occurrence
of `t` lies in a row `n > 2m`, and being an interior entry it satisfies
`C(n,2) ≤ C(n,k) = t`, which caps `n` by an explicit `N` with `t < C(N,2)`.

So the multiplicity of `C(2m,m)` is exactly three as soon as a *finite, explicitly
bounded* search over `2m < n < N`, `2 ≤ k ≤ n/2` finds no further occurrence
(`Singmaster.mult_centralBinom_eq_three`).  The search is phrased with
`Nat.descFactorial` rather than `Nat.choose`, which is what makes it feasible for the
kernel: `C(n,k) = t` is equivalent to `n.descFactorial k = k ! * t`, and the descending
factorial costs `k` multiplications instead of `C(n,k)` additions.

## Results

* `Singmaster.mult_centralBinom_eq_three` — the effective criterion;
* `Singmaster.mult_centralBinom_eq_three_of_le_ten` — `N(C(2m,m)) = 3` for `2 ≤ m ≤ 10`,
  i.e. for `6, 20, 70, 252, 924, 3432, 12870, 48620, 184756`;
* `Singmaster.mult_ne_five_or_seven_of_lt` — **unconditionally, no `t < 705432` occurs
  exactly five or exactly seven times**.  This is the machine-checked version of the
  empirical observation quoted in the problem statement, and it is obtained from only
  ten finite searches rather than from a scan of all `t`;
* `Singmaster.odd_mult_lt_of_lt` — below `705432` an odd multiplicity is `1` or `3`.
-/

open Finset

open Singmaster

/-! ## Basic size estimates for `C(2m,m)` -/





/-! ## The sandwich theorem -/


/-! ## The effective criterion -/



/-! ## Executing the criterion for `m ≤ 10`

Each of the following is a genuine finite search over the explicitly bounded window
produced by the criterion; the windows are empty for `m = 2, 3` and grow to
`20 < n < 609` for `m = 10`. -/











/-! ## Unconditional consequences below `C(22,11) = 705432` -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in

theorem Singmaster.odd_mult_lt_of_lt{t : ℕ} (ht : 2 ≤ t) (hlt : t < 705432) (hodd : Odd (mult t)) :
    mult t = 1 ∨ mult t = 3 := by sorry
