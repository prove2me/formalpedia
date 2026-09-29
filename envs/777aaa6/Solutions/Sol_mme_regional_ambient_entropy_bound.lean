-- Prove2me | solution 1 for mme_regional_ambient_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:18:44.325265+00:00
-- url     : https://prove2.me/submissions/dea39f26-3325-4f63-83fa-f32a6126fa18

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_regional_type_entropy_cover
import Theorems.Thm_mme_regional_same_marginal_integer_entropy_bound
import Mathlib
open BigOperators MME.RecursiveThinSplit MME.RecursiveXHash MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem count_map {A I : Type*} [Fintype A] [DecidableEq A] [DecidableEq I]
    {n : ℕ} (w : Fin n → A) (coord : A → I) (j : I) :
    count (fun t ↦ coord (w t)) j =
      ∑ a : {a // coord a = j}, count w a.val := by
  classical
  let s := Finset.univ.filter (fun a : A ↦ coord a = j)
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) s w
  have hsub := Finset.sum_subtype (F := inferInstance) s
    (fun a ↦ show a ∈ s ↔ coord a = j by simp [s]) (count w)
  rw [← hsub]
  simpa [count, s] using h.symm

private theorem count_sum {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ} (w : Fin n → A) :
    ∑ a, count w a = n := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv w)
  simpa only [Fintype.card_sigma,Fintype.card_subtype,Fintype.card_fin,count] using h

theorem solution {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
    (m : ∀ r, Split half (parent r) → ℕ) (hm : ∀ r, ∑ c, m r c = n r) :
    0 ≤ penaltyPotential n m ∧
    ((ambient (n := n) m).card : ℝ) ≤
      ((((∑ r, n r : ℕ) : ℝ) + 1)) ^ Fintype.card (MME.RecursiveYZ.Cell half R parent) *
        Real.exp (jointPotential m + penaltyPotential n m) := by
  classical
  constructor
  · unfold penaltyPotential
    apply Finset.sum_nonneg
    intro r _
    exact (mme_regional_same_marginal_integer_entropy_bound (m r) (m r) (n r)
      (hm r) (hm r) (fun _ _ ↦ rfl)).1
  · have h := mme_regional_type_entropy_cover n (∑ r, n r)
      (fun r ↦ Finset.single_le_sum (f := n) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r))
      (ambient (n := n) m) (jointPotential m + penaltyPotential n m) (by
        intro w hw
        have hwm : ∀ r, HasMarginalCounts (w r) (m r) := (Finset.mem_filter.mp hw).2
        unfold jointPotential penaltyPotential
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro r _
        have hc := mme_regional_same_marginal_integer_entropy_bound (m r)
          (fun c ↦ count (w r) c) (n r) (hm r) (count_sum (w r)) (by
            intro i j
            exact (count_map (w r) (fun c ↦ c.val i) j).symm.trans (hwm r i j))
        convert hc.2 using 1
        congr 1
        funext c
        congr 1
        unfold count
        congr)
    simpa only [MME.RecursiveYZ.Cell,Fintype.card_sigma] using h
