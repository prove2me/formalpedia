-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.decodeCost_eq_opt_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:00:39.935227+00:00
-- url     : https://prove2.me/submissions/d71dcaef-da1f-4e5f-8a59-d258c3119edf

-- Sol generated from Algebra/ScanSchemeDecoding/Rigidity.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_sum_fiber_card
import Theorems.Thm_ScanSchemeDecoding_sum_triangle_eq_opt_iff

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
theorem solution(hβ : 0 < Fintype.card β) :
    ∑ x, S.decodeCost x = triangleOpt (Fintype.card α) (Fintype.card β) ↔
      ∀ b : β, Fintype.card α / Fintype.card β ≤ (S.fiber b).card ∧
        (S.fiber b).card ≤ Fintype.card α / Fintype.card β + 1 := by
  classical
  set m := Fintype.card β with hm
  let e : β ≃ Fin m := Fintype.equivFin β
  have hsum : ∑ i : Fin m, (S.fiber (e.symm i)).card = Fintype.card α := by
    rw [Equiv.sum_comp e.symm (fun b => (S.fiber b).card)]
    exact S.sum_fiber_card
  have htri : ∑ i : Fin m, triangle (S.fiber (e.symm i)).card
      = ∑ b, triangle (S.fiber b).card :=
    Equiv.sum_comp e.symm (fun b => triangle (S.fiber b).card)
  have hiff := sum_triangle_eq_opt_iff hβ (fun i => (S.fiber (e.symm i)).card)
    (Fintype.card α) hsum
  rw [htri] at hiff
  rw [S.decodeCost_eq, hiff]
  constructor
  · intro h b
    have := h (e b)
    simpa using this
  · intro h i
    exact h (e.symm i)
