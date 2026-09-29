-- Prove2me | solution 1 for Singmaster.centralBinom_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:46:22.148139+00:00
-- url     : https://prove2.me/submissions/806a57cc-6e25-45e2-b498-a4fb2770f053

-- Sol generated from Combinatorics/SingmasterParity.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Theorems.Thm_Singmaster_centralBinom_lt_succ
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






open Singmaster in
theorem solution{m m' : ℕ} (h : (2 * m).choose m = (2 * m').choose m') :
    m = m' := by
  have mono : ∀ p q : ℕ, p < q → (2 * p).choose p < (2 * q).choose q := by
    intro p q hpq
    induction q with
    | zero => omega
    | succ r ih =>
      rcases Nat.lt_or_ge p r with hr | hr
      · exact lt_trans (ih hr) (centralBinom_lt_succ r)
      · have hpr : p = r := by omega
        subst hpr
        exact centralBinom_lt_succ p
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (mono m m' hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (mono m' m hgt))
