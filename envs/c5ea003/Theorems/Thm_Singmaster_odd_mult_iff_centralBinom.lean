-- Prove2me | Theorems.Thm_Singmaster_odd_mult_iff_centralBinom
-- name    : Singmaster.odd_mult_iff_centralBinom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:33:56.655986+00:00
-- url     : https://prove2.me/theorems/eb92a619-7715-4f89-89b7-1898f5525e6d
-- title:
--   **The multiplicity of `t` is odd exactly when `t` is a central binomial
-- statement:
--   **The multiplicity of `t` is odd exactly when `t` is a central binomial
--   coefficient.**  In particular, any number of multiplicity `5` or `7` would have to be
--   of the form `C(2m,m)`.
--
--   ```lean
--   theorem Singmaster.odd_mult_iff_centralBinom{t : ℕ} (ht : 2 ≤ t) :
--       Odd (mult t) ↔ ∃ m, t = (2 * m).choose m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterParity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterParity.lean#L182

-- Thm stub generated from Combinatorics/SingmasterParity.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
/-
# The parity of Singmaster's multiplicity function

Third research cycle.  The empirical mystery quoted in the problem statement is that
no number is known to occur exactly five or exactly seven times, while multiplicities
`1, 2, 3, 4, 6, 8` all occur.  This file isolates the structural reason why *odd*
multiplicities are so rare:

> **`N(t)` is odd if and only if `t` is a central binomial coefficient `C(2m,m)`.**

The proof is a reflection argument.  The symmetry `C(n,k) = C(n,n-k)` is an involution
of the occurrence set `Singmaster.occ t` which exchanges the positions strictly left of
the centre of their row with those strictly right of it; the only positions it fixes
are the central ones `(2m, m)`.  Hence

`N(t) = 2 · #(left positions) + #(central positions)`,

and the central positions are at most one in number, because `m ↦ C(2m,m)` is strictly
increasing.  So an odd multiplicity forces `t = C(2m,m)`.

Consequently the search for a number of multiplicity `5` or `7` can be restricted to
the central binomial coefficients `2, 6, 20, 70, 252, 924, …`.

Main results:
* `Singmaster.mult_eq_two_mul_add_center` — the reflection decomposition;
* `Singmaster.centerOcc_card_le_one` — at most one central occurrence;
* `Singmaster.odd_mult_iff_centralBinom` — the parity criterion;
* `Singmaster.even_mult_of_not_centralBinom` — the contrapositive, in usable form;
* `Singmaster.no_five_or_seven_of_centralBinom_mult_three` — a conditional reduction of
  the `5`/`7` question to the single sequence of central binomial coefficients.
-/

open Finset

open Singmaster

/-! ## Strict growth of the central binomial coefficients -/



/-! ## The reflection decomposition -/










/-! ## At most one central occurrence -/



/-! ## The parity criterion -/

theorem Singmaster.odd_mult_iff_centralBinom{t : ℕ} (ht : 2 ≤ t) :
    Odd (mult t) ↔ ∃ m, t = (2 * m).choose m := by sorry
