-- Prove2me | Theorems.Thm_JacSign_WZ_eq_WN
-- name    : JacSign.WZ_eq_WN
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:36:25.123036+00:00
-- url     : https://prove2.me/theorems/c91c3e8b-c2e5-4b68-8470-b3f60f181b2f
-- title:
--   The abstract Jacobi-signed count coincides with the concrete range-sum.
-- statement:
--   The abstract Jacobi-signed count coincides with the concrete range-sum.
--
--   ```lean
--   theorem JacSign.WZ_eq_WN(n : ℕ) [NeZero n] : WZ n = WN n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedNonDial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedNonDial.lean#L29

-- Thm stub generated from Tropical/JacobiSignedNonDial.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedMultiplicative
import Definitions.Def_Tropical_JacobiSignedNonDial

/-!
# The Jacobi-signed circle count escapes the residue dial

The earlier character-weighted witnesses (CIRC, BQF, GSP) all collapsed to a *residue
dial*: their value was a function of `N mod 4` or `N mod 8`.  Here we prove, by exact
evaluation, that the Jacobi-signed count is **not** a residue dial, and that the Weil
floor of `JacobiSignedWeilFloorBound.lean` is nearly attained.

* `JacSign.WZ_eq_WN` : the abstract statistic equals the concrete range-sum, so all the
  numerical statements below are statements about `W` / `WZ` themselves.
* `JacSign.W_17`, `JacSign.W_41`, ... : exact values (`-2`, `-10`, `-14`, ...).
* `JacSign.not_residue_dial_prime` : there is **no** function `f` with `W p = f (p % 8)`
  for all primes `p`.  (`17 ≡ 41 ≡ 1 (mod 8)` but `W 17 = -2 ≠ -10 = W 41`.)
* `JacSign.not_residue_dial_modulus` : likewise at composite level
  (`21 ≡ 85 ≡ 5 (mod 8)` but `WZ 21 = 0 ≠ -4 = WZ 85`).
* `JacSign.weil_floor_near_attained` : `W 173 = 26` and `26² = 676 > 0.97 · (4 · 173)`,
  so the bound `W p ^ 2 ≤ 4 p` cannot be improved by any constant factor `< 0.977`.
* `JacSign.not_constant_on_primes_mod_four` : the statistic is not a dial mod 4 either.
-/

open Finset

open JacSign

theorem JacSign.WZ_eq_WN(n : ℕ) [NeZero n] : WZ n = WN n := by sorry
