-- Prove2me | solution 1 for Singmaster.mult_eq_two_mul_add_center
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:29:05.914484+00:00
-- url     : https://prove2.me/submissions/64639684-7b11-4d45-b8cb-fbdd9906812a

-- Sol generated from Combinatorics/SingmasterParity.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Theorems.Thm_Singmaster_leftOcc_card_eq_rightOcc_card
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







theorem occ_eq_union (t : ℕ) : occ t = leftOcc t ∪ (rightOcc t ∪ centerOcc t) := by
  ext p
  simp only [leftOcc, rightOcc, centerOcc, mem_union, mem_filter]
  constructor
  · intro h
    rcases lt_trichotomy (2 * p.2) p.1 with hc | hc | hc
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr (Or.inr ⟨h, hc.symm⟩)
    · exact Or.inr (Or.inl ⟨h, hc⟩)
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h



/-! ## At most one central occurrence -/



/-! ## The parity criterion -/






open Singmaster in
theorem solution{t : ℕ} (ht : 2 ≤ t) :
    mult t = 2 * (leftOcc t).card + (centerOcc t).card := by
  classical
  have hdisj1 : Disjoint (rightOcc t) (centerOcc t) := by
    rw [Finset.disjoint_left]
    rintro ⟨n, k⟩ h1 h2
    simp only [rightOcc, centerOcc, mem_filter] at h1 h2
    omega
  have hdisj2 : Disjoint (leftOcc t) (rightOcc t ∪ centerOcc t) := by
    rw [Finset.disjoint_left]
    rintro ⟨n, k⟩ h1 h2
    simp only [leftOcc, rightOcc, centerOcc, mem_union, mem_filter] at h1 h2
    omega
  have hcard : mult t = (leftOcc t).card + ((rightOcc t).card + (centerOcc t).card) := by
    rw [mult, occ_eq_union t, Finset.card_union_of_disjoint hdisj2,
      Finset.card_union_of_disjoint hdisj1]
  rw [hcard, ← leftOcc_card_eq_rightOcc_card ht]
  ring
