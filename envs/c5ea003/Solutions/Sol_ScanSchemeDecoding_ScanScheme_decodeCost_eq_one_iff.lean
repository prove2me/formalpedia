-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.decodeCost_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:50:21.778042+00:00
-- url     : https://prove2.me/submissions/864a5b17-c1d6-4a05-ad79-a7999173a9f4

-- Sol generated from Algebra/ScanSchemeDecoding/Rigidity.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_encode_injective
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_idx_lt_card
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_mem_fiber

/-!
# Rigidity of the optimum, collision-freeness, and symmetry of the cost

The lower bound of `Algebra.ScanSchemeDecoding.Optimum` is not only sharp, it is
*rigid*: the tangent-line argument leaves a slack `(d)(d-1)/2` in each bucket, where
`d` is the deviation of the bucket size from `⌊N/m⌋`.  Since `d(d-1) = 0` only for
`d ∈ {0, 1}`, the optimum is attained **exactly** by the balanced size profiles.

## Main results

* `ScanSchemeDecoding.sum_triangle_eq_opt_iff` — rigidity at the level of size profiles.
* `ScanSchemeDecoding.ScanScheme.decodeCost_eq_opt_iff` — a scan scheme is cost-optimal
  iff every bucket has size `⌊N/m⌋` or `⌈N/m⌉`.
* `ScanSchemeDecoding.ScanScheme.decodeCost_eq_one_iff` — unit decoding cost everywhere
  is *equivalent* to injectivity of the bucket map (perfect hashing).
* `ScanSchemeDecoding.ScanScheme.exists_two_le_decodeCost` — fewer buckets than keys
  forces a key of cost `≥ 2`.
* `ScanSchemeDecoding.ScanScheme.decodeCost_perm_invariant`,
  `ScanSchemeDecoding.ScanScheme.decodeCost_relabel` — the total cost is invariant under
  the natural `Sym(α) × Sym(β)`-action, i.e. it is a function of the bucket-size
  partition alone.
-/

open ScanSchemeDecoding

open Finset


open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)








open ScanSchemeDecoding.ScanScheme in
omit [Fintype β] in
theorem solution: (∀ x, S.decodeCost x = 1) ↔ Function.Injective S.bucket := by
  classical
  constructor
  · intro h x y hxy
    have hx : S.idx x = 0 := by have := h x; simp [decodeCost] at this; omega
    have hy : S.idx y = 0 := by have := h y; simp [decodeCost] at this; omega
    have : S.encode x = S.encode y := by simp [encode, hxy, hx, hy]
    exact S.encode_injective this
  · intro hinj x
    have hfib : S.fiber (S.bucket x) = {x} := by
      ext y
      constructor
      · intro hy
        have : S.bucket y = S.bucket x := by simpa using hy
        simp [hinj this]
      · intro hy
        have : y = x := by simpa using hy
        simp [this]
    have hcard : (S.fiber (S.bucket x)).card = 1 := by rw [hfib]; simp
    have := S.idx_lt_card x
    rw [hcard] at this
    simp [decodeCost]
    omega
