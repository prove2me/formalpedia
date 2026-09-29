-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.exists_two_le_decodeCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:03:41.484533+00:00
-- url     : https://prove2.me/submissions/4fbe5761-3e54-44ef-ad65-2e94b2d3714f

-- Sol generated from Algebra/ScanSchemeDecoding/Rigidity.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq_one_iff

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
theorem solution(h : Fintype.card β < Fintype.card α) :
    ∃ x, 2 ≤ S.decodeCost x := by
  classical
  by_contra hcon
  push_neg at hcon
  have hone : ∀ x, S.decodeCost x = 1 := by
    intro x
    have h1 : 1 ≤ S.decodeCost x := Nat.le_add_left 1 _
    have h2 := hcon x
    omega
  have hinj := (S.decodeCost_eq_one_iff).mp hone
  have := Fintype.card_le_of_injective S.bucket hinj
  omega
