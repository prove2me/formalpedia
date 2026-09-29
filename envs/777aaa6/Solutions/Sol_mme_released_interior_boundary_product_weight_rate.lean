-- Prove2me | solution 1 for mme_released_interior_boundary_product_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:24:45.334277+00:00
-- url     : https://prove2.me/submissions/04ef845e-6efa-4ac0-a98e-562c458cb0cd

import Theorems.Thm_mme_released_interior_boundary_simultaneous_six_weight_rate
import Theorems.Thm_mme_six_square_product_weight
import Mathlib.Tactic.Choose

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary MME.ReleasedInterior Filter
universe u

/-- At one common even replication threshold, every finite family of released
boundary cells combines into a square matrix with the sum of its weight rates.
The family may contain empty cells or repeated cells. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (owner : Fin 6) (s : Fin 45),
      (seed owner s).boundary = [] →
      ∀ (n : ℕ) (c : Fin n → Cell 4 6 (parent s)) (z : Fin n → Fin 3),
      (∀ r, ((c r).2.val (z r)).val = 0) →
    ∃ B : ∀ r, Boundary.Profile 2
        (splitCount owner s (c r).1 (c r).2 +
          splitCount owner s (c r).1 (complement (parent_total s (c r).1) (c r).2)),
      (∀ r i w, integerProfile owner s i (c r) w = (B r).mu (z r) i w) ∧
      ∃ M : ℕ, 0 < M ∧
        (∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K M M M)
            (sixSymmetrization (TensorObj.kronFin n (fun r ↦ CWCells.unbroken K 5 2
              ((2 * k) * (splitCount owner s (c r).1 (c r).2 +
                splitCount owner s (c r).1 (complement (parent_total s (c r).1) (c r).2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => ((c r).2.val i).val)
              (fun i _ w => (2 * k) * integerProfile owner s i (c r) w))))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (∑ r, 6 * tau * (((2 * k : ℕ) : ℝ) *
            (((splitCount owner s (c r).1 (c r).2 +
                splitCount owner s (c r).1 (complement (parent_total s (c r).1) (c r).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((splitCount owner s (c r).1 (c r).2 +
                    splitCount owner s (c r).1 (complement (parent_total s (c r).1) (c r).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by
  classical
  filter_upwards [mme_released_interior_boundary_simultaneous_six_weight_rate.{u}
    delta hdelta] with k hk
  intro owner s hi n c z hz
  have h := fun r => hk owner s (c r) (z r) hi (hz r)
  choose B hmu M hpos hextract hweight using h
  refine ⟨B, hmu, ∏ r, M r, Finset.prod_pos (fun r _ => hpos r), ?_, ?_⟩
  · intro K _
    exact (mme_six_square_product_weight (K := K) _ M _ 0
      (fun r => hextract r K) (fun r => hweight r 0 le_rfl)).1
  · intro tau htau
    exact (mme_six_square_product_weight (K := ULift.{u} ℚ) _ M _ tau
      (fun r => hextract r (ULift.{u} ℚ)) (fun r => hweight r tau htau)).2


#print axioms solution
