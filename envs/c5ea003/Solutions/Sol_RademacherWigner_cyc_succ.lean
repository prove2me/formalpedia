-- Prove2me | solution 1 for RademacherWigner.cyc_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:12:23.291634+00:00
-- url     : https://prove2.me/submissions/a9d2db0a-6b45-4dfc-9170-78f67fe96d4b

-- Sol generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
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
theorem solution{m : ℕ} (i : Fin N) (v : Fin m → Fin N) (t : Fin (m + 1)) :
    cyc m i v (t.val + 1) = (Fin.snoc v i : Fin (m + 1) → Fin N) t := by
  rcases Nat.lt_or_ge t.val m with ht | ht
  · have h2 : cyc m i v (t.val + 1)
        = (Fin.cons i v : Fin (m + 1) → Fin N) ⟨t.val + 1, by omega⟩ := by
      unfold cyc; congr 1; exact Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [h2, show (⟨t.val + 1, by omega⟩ : Fin (m + 1)) = (⟨t.val, ht⟩ : Fin m).succ from rfl,
      Fin.cons_succ]
    calc v ⟨t.val, ht⟩
        = (Fin.snoc v i : Fin (m + 1) → Fin N) (Fin.castSucc ⟨t.val, ht⟩) :=
          (Fin.snoc_castSucc (α := fun _ => Fin N) i v ⟨t.val, ht⟩).symm
      _ = (Fin.snoc v i : Fin (m + 1) → Fin N) t := by congr 1
  · have htm : t = Fin.last m := Fin.ext (by have := t.isLt; simp only [Fin.val_last]; omega)
    have h2 : cyc m i v (t.val + 1) = (Fin.cons i v : Fin (m + 1) → Fin N) 0 := by
      unfold cyc
      congr 1
      refine Fin.ext ?_
      simp [htm]
    rw [h2, htm, Fin.snoc_last, Fin.cons_zero]
