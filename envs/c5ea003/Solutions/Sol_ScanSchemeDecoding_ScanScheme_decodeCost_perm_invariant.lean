-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.decodeCost_perm_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:00:42.393545+00:00
-- url     : https://prove2.me/submissions/4e709826-2592-4c5a-b7b5-698aba208389

-- Sol generated from Algebra/ScanSchemeDecoding/Rigidity.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq
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
theorem solution(sigma : α ≃ α) :
    ∑ x, (⟨S.bucket ∘ sigma⟩ : ScanScheme α β).decodeCost x = ∑ x, S.decodeCost x := by
  classical
  rw [ScanScheme.decodeCost_eq, ScanScheme.decodeCost_eq]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  apply Finset.card_bij' (fun x _ => sigma x) (fun y _ => sigma.symm y)
  · intro x hx
    simpa [ScanScheme.fiber] using hx
  · intro y hy
    have : S.bucket y = b := by simpa using hy
    simpa [ScanScheme.fiber, Function.comp] using this
  · intro x _; simp
  · intro y _; simp
