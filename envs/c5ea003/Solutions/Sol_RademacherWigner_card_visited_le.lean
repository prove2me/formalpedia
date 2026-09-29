-- Prove2me | solution 1 for RademacherWigner.card_visited_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:12:22.773058+00:00
-- url     : https://prove2.me/submissions/30bcc85a-97c3-4896-a09e-5aa80c828b1b

-- Sol generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
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



theorem mem_visited (w : ℕ → Fin N) {s t : ℕ} (hst : s ≤ t) : w s ∈ visited w t :=
  Finset.mem_image_of_mem w (Finset.mem_range.2 (by omega))


/-- If two steps traverse the same edge, the endpoint of the first is an endpoint of
the second. -/
theorem edgeOf_eq_imp {a b c d : Fin N} (h : edgeOf a b = edgeOf c d) : b = c ∨ b = d := by
  unfold edgeOf at h
  split_ifs at h <;> simp_all [Prod.ext_iff]





/-! ### Counting functions with a small image -/


/-! ### From the `Fin`-indexed encoding of a closed walk to a periodic `ℕ`-walk -/








/-! ### The count of even closed walks, and the moment bound -/




/-! ### A matching deterministic lower bound -/







open RademacherWigner in
theorem solution(w : ℕ → Fin N) :
    ∀ t, (visited w t).card ≤ 1 + (edgesUsed w t).card := by
  intro t
  induction t with
  | zero => simp [visited, edgesUsed]
  | succ t ih =>
      have hvis : visited w (t + 1) = insert (w (t + 1)) (visited w t) := by
        simp [visited, Finset.range_add_one, Finset.image_insert, Finset.insert_comm]
      have hedge : edgesUsed w (t + 1) = insert (edgeOf (w t) (w (t + 1))) (edgesUsed w t) := by
        simp [edgesUsed, Finset.range_add_one, Finset.image_insert]
      by_cases hmem : w (t + 1) ∈ visited w t
      · rw [hvis, Finset.insert_eq_self.2 hmem]
        refine ih.trans (Nat.add_le_add_left (Finset.card_le_card ?_) 1)
        rw [hedge]
        exact Finset.subset_insert _ _
      · have hnew : edgeOf (w t) (w (t + 1)) ∉ edgesUsed w t := by
          intro hc
          rw [edgesUsed, Finset.mem_image] at hc
          obtain ⟨s, hs, hse⟩ := hc
          rw [Finset.mem_range] at hs
          rcases edgeOf_eq_imp hse.symm with h | h
          · exact hmem (h ▸ mem_visited w (le_of_lt hs))
          · exact hmem (h ▸ mem_visited w (by omega : s + 1 ≤ t))
        rw [hvis, hedge, Finset.card_insert_of_notMem hnew,
          Finset.card_insert_of_notMem hmem]
        omega
