-- Prove2me | Theorems.Thm_Singmaster_two_le_centralBinom
-- name    : Singmaster.two_le_centralBinom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:31:52.480065+00:00
-- url     : https://prove2.me/theorems/4cd88523-18bd-4e84-95ad-483ed68417c6
-- title:
--   The central binomial coefficient is at least `2`.
-- statement:
--   The central binomial coefficient is at least `2`.
--
--   ```lean
--   theorem Singmaster.two_le_centralBinom{m : ℕ} (hm : 1 ≤ m) : 2 ≤ (2 * m).choose m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterCentralBinomial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterCentralBinomial.lean#L52

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

theorem Singmaster.two_le_centralBinom{m : ℕ} (hm : 1 ≤ m) : 2 ≤ (2 * m).choose m := by sorry
