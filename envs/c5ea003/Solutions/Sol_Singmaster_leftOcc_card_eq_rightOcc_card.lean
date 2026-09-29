-- Prove2me | solution 1 for Singmaster.leftOcc_card_eq_rightOcc_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:27:35.930205+00:00
-- url     : https://prove2.me/submissions/a852bbbc-1f64-40b2-8a1a-345848aa3b53

-- Sol generated from Combinatorics/SingmasterParity.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Theorems.Thm_Singmaster_mem_leftOcc
import Theorems.Thm_Singmaster_mem_occ_iff
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





theorem mem_rightOcc {t n k : ℕ} : (n, k) ∈ rightOcc t ↔ (n, k) ∈ occ t ∧ n < 2 * k :=
  mem_filter





/-! ## At most one central occurrence -/



/-! ## The parity criterion -/






open Singmaster in
theorem solution{t : ℕ} (ht : 2 ≤ t) :
    (leftOcc t).card = (rightOcc t).card := by
  classical
  refine Finset.card_bij (fun p _ => (p.1, p.1 - p.2)) ?_ ?_ ?_
  · rintro ⟨n, k⟩ hp
    rw [mem_leftOcc, mem_occ_iff ht] at hp
    obtain ⟨⟨hk, hck⟩, hlt⟩ := hp
    rw [mem_rightOcc, mem_occ_iff ht]
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    rw [Nat.choose_symm hk]
    exact hck
  · rintro ⟨n, k⟩ hp ⟨n', k'⟩ hp' heq
    rw [mem_leftOcc, mem_occ_iff ht] at hp hp'
    rw [Prod.mk.injEq] at heq
    obtain ⟨hn, hk⟩ := heq
    simp only at hn hk
    subst hn
    rw [Prod.mk.injEq]
    exact ⟨rfl, by omega⟩
  · rintro ⟨n, l⟩ hq
    rw [mem_rightOcc, mem_occ_iff ht] at hq
    obtain ⟨⟨hl, hcl⟩, hgt⟩ := hq
    refine ⟨(n, n - l), ?_, ?_⟩
    · rw [mem_leftOcc, mem_occ_iff ht]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [Nat.choose_symm hl]
      exact hcl
    · rw [Prod.mk.injEq]
      exact ⟨rfl, by omega⟩
