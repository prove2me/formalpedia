-- Prove2me | solution 1 for EmergentGeometry.cutWeight_pair_combination
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:45:57.943609+00:00
-- url     : https://prove2.me/submissions/02ac1236-2539-47c8-a14f-f48193490fd5

-- Sol generated from Novelty/EREPRBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREqualsEPR
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

/-!
# ER = EPR: bulk bridges are exactly boundary entanglement

Building on `Novelty.EmergentGeometryEntropyCone` (min-cut / Ryu–Takayanagi
entropies of a finite bulk geometry) and on `Novelty.EREqualsEPR` (the two-qubit
toy model), this file proves the two halves of the ER=EPR correspondence in the
toy setting:

* **Geometry from entanglement** (`weight_eq_half_mutualInfo`,
  `bulk_weights_determined_by_mutualInfo`): in a model without hidden bulk cells
  every edge weight — i.e. the entire bulk metric — is recovered from
  two-point mutual informations, `w(u,v) = I(u:v)/2`.
* **Entanglement forces a bridge** (`mutualInfo_eq_zero_of_no_bridge`,
  `bridge_of_mutualInfo_pos`): two boundary regions with positive mutual
  information *must* be joined by a positive-weight bulk path, an
  Einstein–Rosen bridge; conversely disconnected regions are unentangled
  (their entropies are exactly additive).
* **EPR ⟺ ER for a qubit pair** (`ER_EPR_correspondence`): a real two-qubit
  pure state is entangled if and only if the associated one-throat geometry,
  whose throat weight is the concurrence, contains a bulk bridge between the
  two boundary qubits.
-/

noncomputable section

open EmergentGeometry

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Boundary regions consisting of one or two cells -/





/-- A Boolean two-point identity: the separation indicators of two disjoint
singletons and of their union differ exactly by the "crossing" indicator. -/
lemma sepBit_two_point (a b c d : Bool) (hab : (a && b) = false) (hcd : (c && d) = false) :
    sepBit a c + sepBit b d
      = sepBit (a || b) (c || d) + (if ((a && d) || (b && c)) = true then 2 else 0) := by
  revert a b c d; decide




/-! ## Bulk connectivity: Einstein–Rosen bridges -/






/-! ## The single-throat geometry of a qubit pair -/





/-! ## Two-qubit states: entanglement is a bridge -/

open EmergentSpacetime







open EmergentGeometry in
theorem solution(G : BulkGraph V) {u v : V} (huv : u ≠ v) :
    cutWeight G (single u) + cutWeight G (single v)
        - cutWeight G (fun x => single u x || single v x)
      = 2 * G.weight u v := by
  have hvu : v ≠ u := Ne.symm huv
  have expand : ∀ (f g h : Region V),
      cutWeight G f + cutWeight G g - cutWeight G h
        = (∑ x, ∑ y, ((sepBit (f x) (f y) : ℝ) + sepBit (g x) (g y)
            - sepBit (h x) (h y)) * G.weight x y) / 2 := by
    intro f g h
    simp only [cutWeight]
    rw [← add_div, ← sub_div]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have key : ∀ x y : V,
      ((sepBit (single u x) (single u y) : ℝ) + sepBit (single v x) (single v y)
        - sepBit (single u x || single v x) (single u y || single v y))
      = (if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then 2 else 0) := by
    intro x y
    have hx : (single u x && single v x) = false := by
      simp only [single, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases h : x = u
      · exact Or.inr (fun h' => huv (h ▸ h'))
      · exact Or.inl h
    have hy : (single u y && single v y) = false := by
      simp only [single, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases h : y = u
      · exact Or.inr (fun h' => huv (h ▸ h'))
      · exact Or.inl h
    have h := sepBit_two_point (single u x) (single v x) (single u y) (single v y) hx hy
    have hR : (if ((single u x && single v y) || (single v x && single u y)) = true
        then (2:ℝ) else 0) = (if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then 2 else 0) := by
      congr 1
      simp [single, Bool.or_eq_true, Bool.and_eq_true]
    have h' : ((sepBit (single u x) (single u y) : ℝ) + sepBit (single v x) (single v y))
        = sepBit (single u x || single v x) (single u y || single v y)
          + (if ((single u x && single v y) || (single v x && single u y)) = true
              then (2:ℝ) else 0) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    rw [← hR]
    linarith [h']
  rw [expand]
  have hcongr : ∀ x : V, ∑ y, ((sepBit (single u x) (single u y) : ℝ)
        + sepBit (single v x) (single v y)
        - sepBit (single u x || single v x) (single u y || single v y)) * G.weight x y
      = ∑ y, (if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then (2:ℝ) else 0) * G.weight x y := by
    intro x
    exact Finset.sum_congr rfl fun y _ => by rw [key x y]
  rw [Finset.sum_congr rfl fun x _ => hcongr x]
  have inner : ∀ x : V,
      ∑ y, (if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then (2:ℝ) else 0) * G.weight x y
      = (if x = u then 2 * G.weight u v else 0) + (if x = v then 2 * G.weight v u else 0) := by
    intro x
    by_cases hxu : x = u
    · have hxv : ¬ (x = v) := fun h => huv (hxu ▸ h)
      have step : ∀ y : V,
          (if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then (2:ℝ) else 0) * G.weight x y
          = if y = v then 2 * G.weight u v else 0 := by
        intro y
        by_cases hy : y = v
        · simp [hxu, hy]
        · simp [hxu, hy, huv]
      rw [Finset.sum_congr rfl fun y _ => step y]
      simp [hxu, huv]
    · by_cases hxv : x = v
      · have step : ∀ y : V,
            (if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then (2:ℝ) else 0) * G.weight x y
            = if y = u then 2 * G.weight v u else 0 := by
          intro y
          by_cases hy : y = u
          · simp [hxv, hy]
          · simp [hxv, hy, hvu]
        rw [Finset.sum_congr rfl fun y _ => step y]
        simp [hxv, hvu]
      · simp [hxu, hxv]
  rw [Finset.sum_congr rfl fun x _ => inner x, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ u (fun _ => 2 * G.weight u v),
    Finset.sum_ite_eq' Finset.univ v (fun _ => 2 * G.weight v u)]
  simp [G.weight_symm v u]
