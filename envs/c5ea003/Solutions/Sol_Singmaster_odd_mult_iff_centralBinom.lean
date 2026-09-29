-- Prove2me | solution 1 for Singmaster.odd_mult_iff_centralBinom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:42:48.436395+00:00
-- url     : https://prove2.me/submissions/47b163fc-af54-421a-b9e9-6287de71061e

-- Sol generated from Combinatorics/SingmasterParity.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Theorems.Thm_Singmaster_centerOcc_card_le_one
import Theorems.Thm_Singmaster_mem_occ
import Theorems.Thm_Singmaster_mem_occ_iff
import Theorems.Thm_Singmaster_mult_eq_two_mul_add_center
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






theorem mem_centerOcc {t n k : ℕ} : (n, k) ∈ centerOcc t ↔ (n, k) ∈ occ t ∧ n = 2 * k :=
  mem_filter




/-! ## At most one central occurrence -/


/-- The central occurrence set is nonempty exactly when `t` is a central binomial
coefficient. -/
theorem centerOcc_nonempty_iff {t : ℕ} (ht : 2 ≤ t) :
    (centerOcc t).Nonempty ↔ ∃ m, t = (2 * m).choose m := by
  constructor
  · rintro ⟨⟨n, k⟩, hp⟩
    rw [mem_centerOcc, mem_occ_iff ht] at hp
    obtain ⟨⟨hk, hck⟩, he⟩ := hp
    subst he
    exact ⟨k, hck.symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨(2 * m, m), ?_⟩
    rw [mem_centerOcc]
    exact ⟨mem_occ ht (by omega) rfl, rfl⟩

/-! ## The parity criterion -/






open Singmaster in
theorem solution{t : ℕ} (ht : 2 ≤ t) :
    Odd (mult t) ↔ ∃ m, t = (2 * m).choose m := by
  classical
  rw [mult_eq_two_mul_add_center ht]
  constructor
  · intro hodd
    have hc : (centerOcc t).card ≠ 0 := by
      rintro h0
      rw [h0] at hodd
      obtain ⟨r, hr⟩ := hodd
      omega
    have hne : (centerOcc t).Nonempty := Finset.card_pos.1 (by omega)
    exact (centerOcc_nonempty_iff ht).1 hne
  · intro hex
    have hne : (centerOcc t).Nonempty := (centerOcc_nonempty_iff ht).2 hex
    have h1 : 1 ≤ (centerOcc t).card := Finset.card_pos.2 hne
    have h2 : (centerOcc t).card ≤ 1 := centerOcc_card_le_one ht
    exact ⟨(leftOcc t).card, by omega⟩
