-- Prove2me | Theorems.Thm_mme_parent_mixture_scale
-- name    : mme_parent_mixture_scale
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:32:54.350993+00:00
-- url     : https://prove2.me/theorems/e8de6d35-cf75-4236-a8eb-3262bf5543bd
-- title:
--   Positive integer replication preserves parent mixtures
-- statement:
--   For any regional parent data, multiply the regional sizes, split counts and child counts by the same positive integer $k$. The resulting parent mixture is unchanged in every region and at every child-word pair:
--   $$P^{(k)}_r(w_0,w_1)=P_r(w_0,w_1).$$
--   Thus replication preserves the centers of the regional histogram windows.
-- source:
--   Integer replication of regional profiles and the released owner-zero (1,1,6) component.

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

theorem mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by sorry
