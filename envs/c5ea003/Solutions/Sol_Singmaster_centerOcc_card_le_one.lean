-- Prove2me | solution 1 for Singmaster.centerOcc_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:52:12.205875+00:00
-- url     : https://prove2.me/submissions/19a38ae4-f029-4ae5-a16d-8ceba2123758

-- Sol generated from Combinatorics/SingmasterParity.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Theorems.Thm_Singmaster_centralBinom_injective
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






theorem mem_centerOcc {t n k : ℕ} : (n, k) ∈ centerOcc t ↔ (n, k) ∈ occ t ∧ n = 2 * k :=
  mem_filter




/-! ## At most one central occurrence -/



/-! ## The parity criterion -/






open Singmaster in
theorem solution{t : ℕ} (ht : 2 ≤ t) : (centerOcc t).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 ?_
  rintro ⟨n, k⟩ h1 ⟨n', k'⟩ h2
  rw [mem_centerOcc, mem_occ_iff ht] at h1 h2
  obtain ⟨⟨_, hv1⟩, he1⟩ := h1
  obtain ⟨⟨_, hv2⟩, he2⟩ := h2
  subst he1
  subst he2
  have hkk : k = k' := centralBinom_injective (by rw [hv1, hv2])
  rw [hkk]
