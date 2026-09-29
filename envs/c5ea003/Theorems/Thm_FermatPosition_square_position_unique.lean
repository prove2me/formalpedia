-- Prove2me | Theorems.Thm_FermatPosition_square_position_unique
-- name    : FermatPosition.square_position_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:29:02.324174+00:00
-- url     : https://prove2.me/theorems/18ce2f98-58fd-48f0-b149-20bb5976e96c
-- title:
--   Square positions of a semiprime sieve.
-- statement:
--   **Square positions of a semiprime sieve.**  If `v(j) = k²` at a position with
--   `1 < b + j - k`, then the position is the terminal Fermat position: `2 (b + j) = p + q`.
--   Every other square position is the trivial factorization `b + j - k = 1`.
--
--   ```lean
--   theorem FermatPosition.square_position_unique{b j k : ℤ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hpq : p ≤ q) (hk : 0 ≤ k) (hu : 1 < b + j - k)
--       (hval : sieveVal b ((p : ℤ) * q) j = k ^ 2) :
--       2 * (b + j) = (p : ℤ) + q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/FermatPositionTerminal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/FermatPositionTerminal.lean#L92

-- Thm stub generated from NumberTheory/FermatPositionTerminal.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionGeometry
/-
# Square positions of the sieve polynomial: the terminal Fermat position

Third companion to `Catalog/NumberTheory/FermatPositionGeometry.lean`.

Among all positions `j` of the sieve polynomial `v(j) = (b + j)^2 - N` the *square*
positions — those with `v(j)` a perfect square — are exactly the factorizations of `N`.
This is Fermat's method, and it gives the one piece of **exactly known** positional
geometry of the smooth locus, against which any statistical claim about hit positions can
be calibrated.

Main results.

* `sieveVal_eq_sq_iff` : `v(j) = k²` iff `N = (b + j - k)(b + j + k)`.
* `sieveVal_at_mid` : writing `N = s² - d²`, the position `s - b` is a square position
  with value `d²`; for `N = p q` with `p + q = 2s`, `q - p = 2d` this is the *terminal
  Fermat position*.
* `terminal_position_bound` : `2 b (s - b) ≤ d²`, i.e. the terminal position obeys the
  same linear magnitude law `2 b j ≤ v(j)` as every other position.  Balanced semiprimes
  (small `d` relative to `√N`) have their terminal position at small `j`; this is a
  *magnitude* statement, not extra positional structure.
* `semiprime_factor_pairs` : the factorizations of a semiprime.
* `square_position_unique` : the only square positions of a semiprime sieve are the
  trivial one (`b + j - k = 1`) and the terminal Fermat position `2 (b + j) = p + q`.
-/

open FermatPosition

theorem FermatPosition.square_position_unique{b j k : ℤ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hk : 0 ≤ k) (hu : 1 < b + j - k)
    (hval : sieveVal b ((p : ℤ) * q) j = k ^ 2) :
    2 * (b + j) = (p : ℤ) + q := by sorry
