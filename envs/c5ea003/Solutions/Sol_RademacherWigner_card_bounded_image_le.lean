-- Prove2me | solution 1 for RademacherWigner.card_bounded_image_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:09:07.947181+00:00
-- url     : https://prove2.me/submissions/59f7936d-ca93-4655-9d38-c45107c8ca28

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
theorem solution{n r : ℕ} (hr : r ≤ N) :
    ((univ : Finset (Fin n → Fin N)).filter
        (fun u => (Finset.image u univ).card ≤ r)).card ≤ N ^ r * r ^ n := by
  classical
  have hsub : ((univ : Finset (Fin n → Fin N)).filter
      (fun u => (Finset.image u univ).card ≤ r))
      ⊆ (Finset.powersetCard r (univ : Finset (Fin N))).biUnion
          fun T => Fintype.piFinset fun _ : Fin n => T := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨T, hT1, hT2⟩ := Finset.exists_superset_card_eq hu.2 (by simpa using hr)
    refine Finset.mem_biUnion.2 ⟨T, Finset.mem_powersetCard.2 ⟨Finset.subset_univ T, hT2⟩, ?_⟩
    exact Fintype.mem_piFinset.2 fun t => hT1 (Finset.mem_image_of_mem u (Finset.mem_univ t))
  calc ((univ : Finset (Fin n → Fin N)).filter
        (fun u => (Finset.image u univ).card ≤ r)).card
      ≤ ((Finset.powersetCard r (univ : Finset (Fin N))).biUnion
          fun T => Fintype.piFinset fun _ : Fin n => T).card := Finset.card_le_card hsub
    _ ≤ ∑ T ∈ Finset.powersetCard r (univ : Finset (Fin N)),
          (Fintype.piFinset fun _ : Fin n => T).card := Finset.card_biUnion_le
    _ = N.choose r * r ^ n := by
        rw [Finset.sum_congr rfl (g := fun _ => r ^ n) ?_]
        · rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
        · intro T hT
          rw [Fintype.card_piFinset, Finset.prod_const, (Finset.mem_powersetCard.1 hT).2]
          simp
    _ ≤ N ^ r * r ^ n := Nat.mul_le_mul_right _ (Nat.choose_le_pow N r)
