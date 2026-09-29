-- Prove2me | solution 1 for RademacherWigner.trace_pow_two_mul_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:56:51.087981+00:00
-- url     : https://prove2.me/submissions/646da4c7-fcfa-4f1b-91c9-4cad337a945b

-- Sol generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Theorems.Thm_RademacherWigner_W_isHermitian
import Theorems.Thm_RademacherWigner_trace_W_sq
import Theorems.Thm_WignerBridge_trace_pow_eq_sum_eigenvalues_real
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
theorem solution(g : Config N) {k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) :
    (N : ℝ) * ((N : ℝ) - 1) ^ k ≤ ((W g) ^ (2 * k)).trace := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hherm := W_isHermitian g
  have heig : ((W g) ^ (2 * (n + 1))).trace
      = ∑ i, (hherm.eigenvalues i ^ 2) ^ (n + 1) := by
    rw [WignerBridge.trace_pow_eq_sum_eigenvalues_real hherm]
    exact Finset.sum_congr rfl fun i _ => by rw [← pow_mul, mul_comm]
  have hsq : (∑ i, hherm.eigenvalues i ^ 2) = (N : ℝ) ^ 2 - (N : ℝ) := by
    rw [← WignerBridge.trace_pow_eq_sum_eigenvalues_real hherm 2, trace_W_sq]
  have hpm := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => hherm.eigenvalues i ^ 2)
    (fun i _ => sq_nonneg _) n
  rw [hsq, Finset.card_univ, Fintype.card_fin,
    show ((N : ℝ) ^ 2 - (N : ℝ)) = (N : ℝ) * ((N : ℝ) - 1) by ring, mul_pow] at hpm
  rw [heig]
  refine le_trans (le_of_eq ?_) hpm
  have hNk : ((N : ℝ) ^ n) ≠ 0 := by positivity
  field_simp
  ring
