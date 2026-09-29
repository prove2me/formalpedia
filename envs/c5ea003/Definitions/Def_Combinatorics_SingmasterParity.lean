-- Prove2me | Definitions.Def_Combinatorics_SingmasterParity
-- name    : Combinatorics_SingmasterParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:49:14.118552+00:00
-- url     : https://prove2.me/theorems/3c4b724f-1c55-4ec3-a62e-89806286ea39
-- title:
--   Aether Catalog definitions — Combinatorics_SingmasterParity
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.SingmasterParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/SingmasterParity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
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

namespace Singmaster

/-! ## Strict growth of the central binomial coefficients -/



/-! ## The reflection decomposition -/

/-- Occurrences strictly left of the centre of their row. -/
def leftOcc (t : ℕ) : Finset (ℕ × ℕ) := (occ t).filter (fun p => 2 * p.2 < p.1)

/-- Occurrences strictly right of the centre of their row. -/
def rightOcc (t : ℕ) : Finset (ℕ × ℕ) := (occ t).filter (fun p => p.1 < 2 * p.2)

/-- Occurrences exactly at the centre of their row. -/
def centerOcc (t : ℕ) : Finset (ℕ × ℕ) := (occ t).filter (fun p => p.1 = 2 * p.2)







/-! ## At most one central occurrence -/



/-! ## The parity criterion -/





end Singmaster


