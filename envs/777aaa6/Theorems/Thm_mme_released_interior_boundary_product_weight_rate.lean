-- Prove2me | Theorems.Thm_mme_released_interior_boundary_product_weight_rate
-- name    : mme_released_interior_boundary_product_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:22:36.808981+00:00
-- url     : https://prove2.me/theorems/b5f5ea53-25c4-4805-ab29-3ebc7956ac88
-- title:
--   Boundary child products attain their summed weight rate
-- statement:
--   At a common even replication threshold, every finite family of boundary children in any released interior recipe admits one positive square-matrix extraction with the sum of its entropy and letter-weight rates. Empty and repeated cells are allowed. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_boundary_simultaneous_six_weight_rate
import Theorems.Thm_mme_six_square_product_weight
import Mathlib.Tactic.Choose
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary MME.ReleasedInterior Filter
universe u

theorem mme_released_interior_boundary_product_weight_rate
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
            ((M * M * M : ℕ) : ℝ) ^ tau := by sorry
