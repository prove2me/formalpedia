-- Prove2me | solution 1 for Singmaster.no_five_or_seven_of_centralBinom_mult_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:56:17.938804+00:00
-- url     : https://prove2.me/submissions/4da844f1-d69b-4408-ab10-baa7225cea4b

-- Sol generated from Combinatorics/SingmasterParity.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Theorems.Thm_Singmaster_mult_two
import Theorems.Thm_Singmaster_odd_mult_iff_centralBinom
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



/-- **Consequence for Singmaster's `5`/`7` question.**  If some number occurs exactly
five (or exactly seven) times, it is a central binomial coefficient. -/
theorem centralBinom_of_mult_five_or_seven {t : ℕ} (ht : 2 ≤ t)
    (h : mult t = 5 ∨ mult t = 7) : ∃ m, t = (2 * m).choose m := by
  refine (odd_mult_iff_centralBinom ht).1 ?_
  rcases h with h | h <;> rw [h]
  · exact ⟨2, by norm_num⟩
  · exact ⟨3, by norm_num⟩



open Singmaster in
theorem solution    (H : ∀ m, 2 ≤ m → mult ((2 * m).choose m) = 3) {t : ℕ} (ht : 2 ≤ t) :
    mult t ≠ 5 ∧ mult t ≠ 7 := by
  constructor <;> intro hcon
  · obtain ⟨m, hm⟩ := centralBinom_of_mult_five_or_seven ht (Or.inl hcon)
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      · rw [hm] at ht; norm_num at ht
      · rw [hm] at hcon
        norm_num [mult_two] at hcon
    · rw [hm] at hcon
      rw [H m hge] at hcon
      omega
  · obtain ⟨m, hm⟩ := centralBinom_of_mult_five_or_seven ht (Or.inr hcon)
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      · rw [hm] at ht; norm_num at ht
      · rw [hm] at hcon
        norm_num [mult_two] at hcon
    · rw [hm] at hcon
      rw [H m hge] at hcon
      omega
