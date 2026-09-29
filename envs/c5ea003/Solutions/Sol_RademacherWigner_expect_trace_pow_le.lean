-- Prove2me | solution 1 for RademacherWigner.expect_trace_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:45:40.03535+00:00
-- url     : https://prove2.me/submissions/d547f5f0-b09d-4a71-bfb7-bbe473d386e4

-- Sol generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Theorems.Thm_RademacherWigner_card_filter_le_pow
import Theorems.Thm_RademacherWigner_card_image_cons_le_of_ne_one
import Theorems.Thm_RademacherWigner_expect_trace_pow_eq_sum_indicator
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Polynomial growth of every even moment: tightness of the empirical spectral law

`Probability.WignerAllOrderParity` reduces the computation of every trace moment of
the symmetric Rademacher ensemble to a count of *even closed walks* — loop-free
closed walks all of whose edge multiplicities are even — and proves that the odd
moments vanish identically.  This file supplies the missing quantitative half at
even order: an even closed walk of length `2k` can visit at most `k + 1` distinct
vertices, so there are at most `N^(k+1) (k+1)^(2k)` of them and

  `E [ tr (W ^ (2k)) ] ≤ N^(k+1) · (k+1)^(2k)`,
  `E [ (1/N) tr ((W/√N) ^ (2k)) ] ≤ (k+1)^(2k)`   (uniformly in `N`).

The structural core is graph-theoretic and is proved from scratch here:

* `RademacherWigner.card_visited_le` — along any walk, the number of vertices
  visited never exceeds `1 +` the number of distinct edges used (a spanning-tree
  bound, proved by induction on the length of the walk);
* `RademacherWigner.card_edgesUsed_le` — if every edge multiplicity is even, then
  twice the number of distinct edges is at most the length of the walk;
* `RademacherWigner.card_visited_le_of_even` — combining the two, an even closed
  walk of `2k` steps visits at most `k + 1` vertices;
* `RademacherWigner.card_bounded_image_le` — a function `Fin n → Fin N` whose image
  has at most `r` elements is determined by an `r`-element subset together with a
  map into it, giving at most `N^r · r^n` such functions.

Uniform boundedness of all normalised moments is exactly the tightness input of the
moment method: together with `expect_trace_pow_odd` it says that the expected
empirical spectral distribution of `W/√N` has moments that neither blow up nor
oscillate with `N`, at *every* order.
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}

/-! ### Vertices and edges visited by a walk -/










/-! ### Counting functions with a small image -/


/-! ### From the `Fin`-indexed encoding of a closed walk to a periodic `ℕ`-walk -/







/-- **Even closed walks are thin.**  An even closed walk of `2k` steps visits at most
`k + 1` distinct vertices. -/
theorem card_image_cons_le_of_isEvenWalk {m k : ℕ} (hm : m + 1 = 2 * k) {i : Fin N}
    {v : Fin m → Fin N} (h : IsEvenWalk m i v) :
    (Finset.image (Fin.cons i v : Fin (m + 1) → Fin N) univ).card ≤ k + 1 := by
  refine card_image_cons_le_of_ne_one (by omega) fun p hp => ?_
  obtain ⟨c, hc⟩ := h.2 p
  omega

/-! ### The count of even closed walks, and the moment bound -/


/-- There are at most `N^(k+1) (k+1)^(2k)` even closed walks of length `2k`. -/
theorem card_evenWalks_le {m k : ℕ} (hm : m + 1 = 2 * k) :
    ((univ : Finset (Fin N × (Fin m → Fin N))).filter fun x => IsEvenWalk m x.1 x.2).card
      ≤ N ^ (k + 1) * (k + 1) ^ (m + 1) :=
  card_filter_le_pow (N := N) (by omega) _ fun _ hx => card_image_cons_le_of_isEvenWalk hm hx


/-! ### A matching deterministic lower bound -/







open RademacherWigner in
theorem solution{m k : ℕ} (hm : m + 1 = 2 * k) :
    expect (fun g : Config N => ((W g) ^ (m + 1)).trace)
      ≤ (N : ℝ) ^ (k + 1) * ((k : ℝ) + 1) ^ (m + 1) := by
  have hcount : expect (fun g : Config N => ((W g) ^ (m + 1)).trace)
      = (((univ : Finset (Fin N × (Fin m → Fin N))).filter
          fun x => IsEvenWalk m x.1 x.2).card : ℝ) := by
    rw [expect_trace_pow_eq_sum_indicator, ← Finset.sum_boole, Fintype.sum_prod_type]
  rw [hcount]
  have h := card_evenWalks_le (N := N) hm
  have hcast : (((univ : Finset (Fin N × (Fin m → Fin N))).filter
      fun x => IsEvenWalk m x.1 x.2).card : ℝ) ≤ ((N ^ (k + 1) * (k + 1) ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast h
  refine hcast.trans (le_of_eq ?_)
  push_cast
  ring
