-- Prove2me | solution 1 for RademacherWigner.card_edgesUsed_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:09:09.19158+00:00
-- url     : https://prove2.me/submissions/8a1821fa-e028-4147-8408-fecefaa3338f

-- Sol generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerWalkParity
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








/-! ### The count of even closed walks, and the moment bound -/




/-! ### A matching deterministic lower bound -/







open RademacherWigner in
theorem solution(w : ℕ → Fin N) (n : ℕ)
    (hne1 : ∀ p, edgeCount n w p ≠ 1) : 2 * (edgesUsed w n).card ≤ n := by
  have hmaps : ∀ s ∈ Finset.range n, edgeOf (w s) (w (s + 1)) ∈ edgesUsed w n :=
    fun s hs => Finset.mem_image_of_mem _ hs
  have hfib : n = ∑ p ∈ edgesUsed w n, edgeCount n w p := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun s => edgeOf (w s) (w (s + 1))) (s := Finset.range n) (t := edgesUsed w n) hmaps
    simpa [edgeCount, Finset.card_range] using h
  have hge : ∀ p ∈ edgesUsed w n, 2 ≤ edgeCount n w p := by
    intro p hp
    have hpos : 0 < edgeCount n w p := by
      rw [edgesUsed, Finset.mem_image] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      rw [edgeCount, Finset.card_pos]
      exact ⟨s, Finset.mem_filter.2 ⟨hs, rfl⟩⟩
    have := hne1 p
    omega
  calc 2 * (edgesUsed w n).card
      = ∑ _p ∈ edgesUsed w n, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ edgesUsed w n, edgeCount n w p := Finset.sum_le_sum hge
    _ = n := hfib.symm
