-- Prove2me | Theorems.Thm_mme_released_interior_mixed_child_product_weight_rate
-- name    : mme_released_interior_mixed_child_product_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:52:13.294495+00:00
-- url     : https://prove2.me/theorems/a2dc4371-9bce-4bd1-b961-9c944ac8ea62
-- title:
--   Boundary and 112 products combine at a common physical scale
-- statement:
--   The boundary square-matrix product and the 112 matrix-family product combine into an actual extraction from their physical tensor product. Their certified weight exponents add, the output copy count stays positive, and empty cells are included on either side. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_boundary_product_weight_rate
import Theorems.Thm_mme_released_interior_112_product_weight_rate
import Theorems.Thm_mme_six_square_family_product_weight
open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open MME.RecursiveYZ.Boundary
open scoped BigOperators
universe u

theorem mme_released_interior_mixed_child_product_weight_rate
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (owner : Fin 6) (s : Fin 45),
      (seed owner s).boundary = [] →
      ∀ (nB : ℕ) (cB : Fin nB → Cell 4 6 (parent s)) (zB : Fin nB → Fin 3),
      (∀ t, ((cB t).2.val (zB t)).val = 0) →
      ∀ (nI : ℕ) (cI : Fin nI → Cell 4 6 (parent s)) (zI : Fin nI → Fin 3),
      (∀ t i, ((cI t).2.val i).val = if i = zI t then 2 else 1) →
    ∃ B : ∀ r, Boundary.Profile 2
        (splitCount owner s (cB r).1 (cB r).2 +
          splitCount owner s (cB r).1 (complement (parent_total s (cB r).1) (cB r).2)),
      (∀ r i w, integerProfile owner s i (cB r) w = (B r).mu (zB r) i w) ∧
      ∀ (K : Type u) [Field K] (tau : ℝ), 0 ≤ tau →
      ∃ (copies : ℕ) (a b d : Fin copies → ℕ), 0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
          (sixSymmetrization (TensorObj.kron
            (TensorObj.kronFin nB (fun r ↦ CWCells.unbroken K 5 2
              ((2 * k) * (splitCount owner s (cB r).1 (cB r).2 +
                splitCount owner s (cB r).1 (complement (parent_total s (cB r).1) (cB r).2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => ((cB r).2.val i).val)
              (fun i _ w => (2 * k) * integerProfile owner s i (cB r) w)))
            (TensorObj.kronFin nI (fun t =>
            CWCells.unbroken K 5 2
              ((2 * k) * (splitCount owner s (cI t).1 (cI t).2 +
                splitCount owner s (cI t).1
                  (complement (parent_total s (cI t).1) (cI t).2)))
              (Equiv.refl _) (fun _ => Unit.unit) (fun _ i => ((cI t).2.val i).val)
              (fun i _ w => (2 * k) * integerProfile owner s i (cI t) w))))) ∧
        Real.exp ((∑ r, 6 * tau * (((2 * k : ℕ) : ℝ) *
            (((splitCount owner s (cB r).1 (cB r).2 +
                splitCount owner s (cB r).1 (complement (parent_total s (cB r).1) (cB r).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((splitCount owner s (cB r).1 (cB r).2 +
                    splitCount owner s (cB r).1 (complement (parent_total s (cB r).1) (cB r).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) + (∑ t,
      let m := k * ((seed owner s).region.getD (cI t).1.val 0 *
        (splitWeight owner s (cI t).1 (cI t).2 +
          splitWeight owner s (cI t).1 (complement (parent_total s (cI t).1) (cI t).2)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == (cI t).1.val && a.2.1 == sourceShape owner (cI t).2)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == (cI t).1.val && a.2.1 == sourceShape owner (cI t).2)).getD (0, [], 0)).2.2)) * m
      let p : ℝ :=
        (((((seed owner s).children.find?
          (fun a => a.1 == (cI t).1.val && a.2.1 == sourceShape owner (cI t).2)).getD
            (0, [], 0)).2.2) : ℝ) / denominator
      ((4 * N : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 )) ≤
          ∑ j, (((a j * b j * d j : ℕ) : ℝ) ^ tau) := by sorry
