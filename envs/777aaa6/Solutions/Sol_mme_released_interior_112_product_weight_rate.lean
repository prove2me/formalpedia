-- Prove2me | solution 1 for mme_released_interior_112_product_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:47:49.862716+00:00
-- url     : https://prove2.me/submissions/94b44626-75c0-4492-963c-a9040a7eb073

import Theorems.Thm_mme_released_interior_112_all_cells_six_weight_rate
import Theorems.Thm_mme_six_product_exponential_extraction

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open scoped BigOperators
universe u

/-- At a common even replication threshold, every finite family of released
112 children attains the sum of its entropy and matrix-volume weight rates.
Empty cells and zero outer parameters are included. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (owner : Fin 6) (s : Fin 45)
      (n : ℕ) (c : Fin n → Cell 4 6 (parent s)) (z : Fin n → Fin 3),
      (∀ t i, ((c t).2.val i).val = if i = z t then 2 else 1) →
      ∀ (K : Type u) [Field K] (tau : ℝ),
      ∃ (copies : ℕ) (a b d : Fin copies → ℕ), 0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
          (sixSymmetrization (TensorObj.kronFin n (fun t =>
            CWCells.unbroken K 5 2
              ((2 * k) * (splitCount owner s (c t).1 (c t).2 +
                splitCount owner s (c t).1
                  (complement (parent_total s (c t).1) (c t).2)))
              (Equiv.refl _) (fun _ => Unit.unit) (fun _ i => ((c t).2.val i).val)
              (fun i _ w => (2 * k) * integerProfile owner s i (c t) w)))) ∧
        Real.exp (∑ t,
      let m := k * ((seed owner s).region.getD (c t).1.val 0 *
        (splitWeight owner s (c t).1 (c t).2 +
          splitWeight owner s (c t).1 (complement (parent_total s (c t).1) (c t).2)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == (c t).1.val && a.2.1 == sourceShape owner (c t).2)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == (c t).1.val && a.2.1 == sourceShape owner (c t).2)).getD (0, [], 0)).2.2)) * m
      let p : ℝ :=
        (((((seed owner s).children.find?
          (fun a => a.1 == (c t).1.val && a.2.1 == sourceShape owner (c t).2)).getD
            (0, [], 0)).2.2) : ℝ) / denominator
      ((4 * N : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 ) ≤ ∑ j, (((a j * b j * d j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [mme_released_interior_112_all_cells_six_weight_rate delta hdelta]
    with k hk
  intro owner s n c z hshape K _ tau
  apply mme_six_product_exponential_extraction
  intro t
  obtain ⟨copies, a, b, d, _, hrestrict, _, hweight⟩ :=
    hk owner s (c t).1 (c t).2 (z t) (hshape t) K
  exact ⟨copies, a, b, d, hrestrict, hweight tau⟩


#print axioms solution
