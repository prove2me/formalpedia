-- Prove2me | solution 1 for mme_certified_regional_rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:17:17.139052+00:00
-- url     : https://prove2.me/submissions/d213cef5-7aef-4a4f-ab9f-4c853c38a34d

import Mathlib
import Definitions.Def_mme_certified_generic_rate_data
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Theorems.Thm_mme_certified_parent_potential_floor
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_entropy_penalty_rational

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000


namespace MME.Cert

variable {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}

/-- A certified rational floor for a coarse potential, from per-region reference tables. -/
theorem coarsePotential_floorG
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3)
    (hpos : ∀ r, 0 < ∑ j, marginalCounts m i r j)
    (e : Fin R → Fin (half + 1) → Fin 4 → ℤ) (f : Fin R → ℚ)
    (hf : ∀ r, f r ≤ regFloorG (normQ (marginalCounts m i r)) (e r)) :
    (∑ r : Fin R, ((∑ j, marginalCounts m i r j : ℕ) : ℝ) * ((f r : ℚ) : ℝ)) ≤
      coarsePotential m i := by
  rw [mme_certified_entropy_bridge.{0, 0}.2.2.2.2.2 m i hpos]
  refine Finset.sum_le_sum (fun r _ ↦ ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ?_ (mme_certified_parent_potential_floor.1
    (normQ (marginalCounts m i r))
    (fun j ↦ mme_certified_entropy_bridge.{0, 0}.2.2.2.2.1 (marginalCounts m i r) j) (e r))
  exact_mod_cast hf r

theorem alphaG_nonneg (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (r : Fin R)
    (c : RecursiveThinSplit.Split half (parent r)) : 0 ≤ alphaG n m r c := by
  unfold alphaG
  positivity

theorem alphaG_sum (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (r : Fin R)
    (hn : 0 < n r) (hm : ∑ c, m r c = n r) :
    ∑ c : RecursiveThinSplit.Split half (parent r), alphaG n m r c = 1 := by
  have hq : ((n r : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold alphaG
  rw [← Finset.sum_div, ← Nat.cast_sum, hm]
  exact div_self hq

/-- A certified rational ceiling for a whole penalty potential. -/
theorem penaltyPotential_ceilG (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (hn : ∀ r, 0 < n r) (hm : ∀ r, ∑ c, m r c = n r)
    (E : Fin R → Fin 3 → Fin (half + 1) → (Fin 4 → ℤ)) (g : Fin R → ℚ)
    (hg : ∀ r, ((∑ c : RecursiveThinSplit.Split half (parent r),
        qvalQ (fun k ↦ ∑ i, E r i (c.val i) k)) - 2 +
      ∑ c : RecursiveThinSplit.Split half (parent r),
        (alphaG n m r c) ^ 2 / qvalQ (fun k ↦ ∑ i, E r i (c.val i) k)) ≤ g r) :
    penaltyPotential n m ≤ ∑ r : Fin R, ((n r : ℕ) : ℝ) * ((g r : ℚ) : ℝ) := by
  unfold penaltyPotential
  refine Finset.sum_le_sum (fun r _ ↦ ?_)
  have hcast : (fun c : RecursiveThinSplit.Split half (parent r) ↦
      (m r c : ℝ) / ((n r : ℕ) : ℝ)) = fun c ↦ ((alphaG n m r c : ℚ) : ℝ) := by
    funext c
    unfold alphaG
    push_cast
    ring
  rw [mul_assoc, hcast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (mme_certified_entropy_penalty_rational (alphaG n m r)
    (alphaG_nonneg n m r) (alphaG_sum n m r (hn r) (hm r)) (E r)) ?_
  exact_mod_cast hg r


end MME.Cert

theorem solution :
    (∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
      (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3),
      (∀ r, 0 < ∑ j, marginalCounts m i r j) →
      ∀ (e : Fin R → Fin (half + 1) → Fin 4 → ℤ) (f : Fin R → ℚ),
      (∀ r, f r ≤ regFloorG (normQ (marginalCounts m i r)) (e r)) →
      (∑ r : Fin R, ((∑ j, marginalCounts m i r j : ℕ) : ℝ) * ((f r : ℚ) : ℝ)) ≤
        coarsePotential m i) ∧
    ∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
      (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ),
      (∀ r, 0 < n r) → (∀ r, ∑ c, m r c = n r) →
      ∀ (E : Fin R → Fin 3 → Fin (half + 1) → (Fin 4 → ℤ)) (g : Fin R → ℚ),
      (∀ r, ((∑ c : RecursiveThinSplit.Split half (parent r),
          qvalQ (fun k ↦ ∑ i, E r i (c.val i) k)) - 2 +
        ∑ c : RecursiveThinSplit.Split half (parent r),
          (alphaG n m r c) ^ 2 / qvalQ (fun k ↦ ∑ i, E r i (c.val i) k)) ≤ g r) →
      penaltyPotential n m ≤ ∑ r : Fin R, ((n r : ℕ) : ℝ) * ((g r : ℚ) : ℝ) :=
  ⟨fun {half} {R} {parent} m i hpos e f hf ↦ MME.Cert.coarsePotential_floorG m i hpos e f hf,
   fun {half} {R} {parent} n m hn hm E g hg ↦ MME.Cert.penaltyPotential_ceilG n m hn hm E g hg⟩
