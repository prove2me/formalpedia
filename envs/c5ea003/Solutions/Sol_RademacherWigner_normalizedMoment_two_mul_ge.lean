-- Prove2me | solution 1 for RademacherWigner.normalizedMoment_two_mul_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:59:39.861027+00:00
-- url     : https://prove2.me/submissions/73aba4a8-bb77-4a75-9b03-f6976f1ce609

-- Sol generated from Probability/WignerMomentGrowth.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_trace_pow_two_mul_ge
import Theorems.Thm_WignerBridge_normalizedMoment_eq
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
    (1 - 1 / (N : ℝ)) ^ k ≤ WignerBridge.normalizedMoment (W g) (2 * k) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : (Fintype.card (Fin N) : ℝ) = (N : ℝ) := by simp
  have hsq : (Real.sqrt (Fintype.card (Fin N)))⁻¹ ^ (2 * k) = ((N : ℝ) ^ k)⁻¹ := by
    rw [hcard, pow_mul, ← Real.sqrt_inv, Real.sq_sqrt (by positivity), inv_pow]
  rw [WignerBridge.normalizedMoment_eq, hsq, hcard]
  have hpos : (0 : ℝ) < 1 / (N : ℝ) * ((N : ℝ) ^ k)⁻¹ := by positivity
  have h := trace_pow_two_mul_ge g hk hN
  calc (1 - 1 / (N : ℝ)) ^ k
      = (1 / (N : ℝ) * ((N : ℝ) ^ k)⁻¹) * ((N : ℝ) * ((N : ℝ) - 1) ^ k) := by
        rw [show (1 : ℝ) - 1 / (N : ℝ) = ((N : ℝ) - 1) / (N : ℝ) by field_simp, div_pow]
        field_simp
    _ ≤ (1 / (N : ℝ) * ((N : ℝ) ^ k)⁻¹) * ((W g) ^ (2 * k)).trace :=
        mul_le_mul_of_nonneg_left h (le_of_lt hpos)
    _ = 1 / (N : ℝ) * ((N : ℝ) ^ k)⁻¹ * ((W g) ^ (2 * k)).trace := rfl
