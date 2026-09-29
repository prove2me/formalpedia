-- Prove2me | solution 1 for RademacherWigner.card_filter_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:12:21.770985+00:00
-- url     : https://prove2.me/submissions/692bf07e-1b6d-4d44-b50d-ef09b75e5333

-- Sol generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
import Theorems.Thm_RademacherWigner_card_bounded_image_le
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
theorem solution{m k : ℕ} (hkm : k ≤ m) (P : Fin N × (Fin m → Fin N) → Prop)
    [DecidablePred P]
    (hP : ∀ x, P x →
      (Finset.image (Fin.cons x.1 x.2 : Fin (m + 1) → Fin N) univ).card ≤ k + 1) :
    ((univ : Finset (Fin N × (Fin m → Fin N))).filter P).card
      ≤ N ^ (k + 1) * (k + 1) ^ (m + 1) := by
  by_cases hNk : k + 1 ≤ N
  · refine le_trans (Finset.card_le_card_of_injOn
      (fun x => (Fin.cons x.1 x.2 : Fin (m + 1) → Fin N)) ?_ ?_)
      (card_bounded_image_le (n := m + 1) (r := k + 1) hNk)
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hP x hx.2⟩
    · intro x _ y _ hxy
      have h0 : x.1 = y.1 := by
        have := congrFun hxy 0
        simpa using this
      have h1 : x.2 = y.2 := by
        funext t
        have := congrFun hxy t.succ
        simpa using this
      exact Prod.ext h0 h1
  · push_neg at hNk
    have hcard : ((univ : Finset (Fin N × (Fin m → Fin N))).filter P).card ≤ N ^ (m + 1) := by
      refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
      simp [Finset.card_univ, Fintype.card_prod, pow_succ, mul_comm]
    refine hcard.trans ?_
    have hsplit : N ^ (m + 1) = N ^ (k + 1) * N ^ (m - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    refine Nat.mul_le_mul_left _ ?_
    calc N ^ (m - k) ≤ (k + 1) ^ (m - k) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (k + 1) ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
