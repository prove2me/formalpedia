-- Prove2me | solution 1 for RademacherWigner.card_image_cons_le_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:14:13.970646+00:00
-- url     : https://prove2.me/submissions/d0ec4445-bca9-49d7-b0de-8858d4fbf1bd

-- Sol generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerWalkParity
import Theorems.Thm_RademacherWigner_card_edgesUsed_le
import Theorems.Thm_RademacherWigner_card_visited_le
import Theorems.Thm_RademacherWigner_cyc_succ
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




theorem edgesUsed_mono (w : ℕ → Fin N) {s t : ℕ} (hst : s ≤ t) :
    edgesUsed w s ⊆ edgesUsed w t := by
  intro e he
  rw [edgesUsed, Finset.mem_image] at he ⊢
  obtain ⟨u, hu, rfl⟩ := he
  rw [Finset.mem_range] at hu
  exact ⟨u, Finset.mem_range.2 (by omega), rfl⟩




/-- A closed walk of `m + 1` steps no edge of which is traversed exactly once visits
at most `(m + 3) / 2` vertices. -/
theorem card_visited_le_of_ne_one (w : ℕ → Fin N) (m : ℕ)
    (hne1 : ∀ p, edgeCount (m + 1) w p ≠ 1) : 2 * (visited w m).card ≤ m + 3 := by
  have h1 := card_visited_le w m
  have h2 : (edgesUsed w m).card ≤ (edgesUsed w (m + 1)).card :=
    Finset.card_le_card (edgesUsed_mono w (Nat.le_succ m))
  have h3 := card_edgesUsed_le w (m + 1) hne1
  omega


/-! ### Counting functions with a small image -/


/-! ### From the `Fin`-indexed encoding of a closed walk to a periodic `ℕ`-walk -/


theorem cyc_apply {m : ℕ} (i : Fin N) (v : Fin m → Fin N) (t : Fin (m + 1)) :
    cyc m i v t.val = (Fin.cons i v : Fin (m + 1) → Fin N) t := by
  unfold cyc
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt t.isLt)


theorem edgeMult_eq_edgeCount {m : ℕ} (i : Fin N) (v : Fin m → Fin N) (p : Fin N × Fin N) :
    edgeMult (Fin.cons i v : Fin (m + 1) → Fin N) (Fin.snoc v i : Fin (m + 1) → Fin N) p
      = edgeCount (m + 1) (cyc m i v) p := by
  rw [edgeMult, Finset.card_filter, edgeCount, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range
      (fun t => if edgeOf (cyc m i v t) (cyc m i v (t + 1)) = p then 1 else 0) (m + 1)]
  exact Finset.sum_congr rfl fun t _ => by rw [cyc_apply, cyc_succ]

theorem image_cons_eq_visited {m : ℕ} (i : Fin N) (v : Fin m → Fin N) :
    Finset.image (Fin.cons i v : Fin (m + 1) → Fin N) univ = visited (cyc m i v) m := by
  ext x
  simp only [visited, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.val, t.isLt, cyc_apply i v t⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, (cyc_apply i v ⟨s, hs⟩).symm⟩



/-! ### The count of even closed walks, and the moment bound -/




/-! ### A matching deterministic lower bound -/







open RademacherWigner in
theorem solution{m k : ℕ} (hm : m ≤ 2 * k) {i : Fin N}
    {v : Fin m → Fin N}
    (h : ∀ p, edgeMult (Fin.cons i v : Fin (m + 1) → Fin N)
      (Fin.snoc v i : Fin (m + 1) → Fin N) p ≠ 1) :
    (Finset.image (Fin.cons i v : Fin (m + 1) → Fin N) univ).card ≤ k + 1 := by
  have hne1 : ∀ p, edgeCount (m + 1) (cyc m i v) p ≠ 1 := by
    intro p
    rw [← edgeMult_eq_edgeCount]
    exact h p
  have h1 := card_visited_le_of_ne_one (cyc m i v) m hne1
  rw [image_cons_eq_visited]
  omega
