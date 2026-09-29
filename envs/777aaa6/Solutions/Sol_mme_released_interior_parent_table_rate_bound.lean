-- Prove2me | solution 1 for mme_released_interior_parent_table_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T23:10:02.896986+00:00
-- url     : https://prove2.me/submissions/f35265e2-2c31-40ec-99cc-85ff3e2f54f1

import Theorems.Thm_mme_boundary_table_weight_rate_bound
import Theorems.Thm_mme_112_table_weight_rate_bound
import Theorems.Thm_mme_released_interior_child_partition_loss_bound
import Theorems.Thm_mme_released_interior_cell_child_parameter_bound
import Theorems.Thm_mme_released_interior_child_mass_bounds

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedInterior MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.CompleteSplit MME.RecursiveYZ.Boundary

/-- A complete actual child table bounds the rate of any extracted parent
partition, with one uniform error budget for all its children. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (k : ℕ)
    (tau delta bound : ℝ) (htau : tau ≤ 1) (hdelta : 0 ≤ delta)
    (q : Cell 4 6 (parent s) → ℝ) (hsum : bound ≤ ∑ c, q c)
    (hboundary : ∀ c z, (c.2.val z).val = 0 →
        (denominator : ℝ) ^ 4 * q c ≤ 6 * tau *
          (massEntropy (fun w ↦ (integerProfile owner s (z + 1) c w : ℝ)) +
            (∑ w, (integerProfile owner s (z + 1) c w : ℝ) * (ones w : ℝ)) * Real.log 5))
    (hinterior : ∀ c z, (∀ i : Fin 3, (c.2.val i).val = if i = z then 2 else 1) →
        let p : ℝ := ((((seed owner s).children.find?
          (fun a => a.1 == c.1.val && a.2.1 == sourceShape owner c.2)).getD (0, [], 0)).2.2 : ℝ) / denominator
        q c ≤ (((seed owner s).region.getD c.1.val 0 : ℝ) / denominator *
          ((splitWeight owner s c.1 c.2 + splitWeight owner s c.1
            (complement (parent_total s c.1) c.2) : ℕ) : ℝ) / denominator / 2) *
          (4 * (entropy ![p, p, 1 - 2 * p] + 2 * Real.log 2) +
            24 * (1 - p) * tau * Real.log 5))
    (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (parent s))
    (zB : Fin nB → Fin 3) (zI : Fin nI → Fin 3)
    (hzB : ∀ j, ((e (.inl j)).2.val (zB j)).val = 0)
    (hzI : ∀ j i, ((e (.inr j)).2.val i).val = if i = zI j then 2 else 1)
    (B : ∀ r, Boundary.Profile 2
      (splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
        splitCount owner s (e (.inl r)).1
          (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2)))
    (hmu : ∀ r i w, integerProfile owner s i (e (.inl r)) w = (B r).mu (zB r) i w) :
    ((2 * k : ℕ) : ℝ) * (denominator : ℝ) ^ 4 * (bound - 540 * delta) ≤
      ((∑ r, 6 * tau * (((2 * k : ℕ) : ℝ) *
            (((splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
                splitCount owner s (e (.inl r)).1 (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
                    splitCount owner s (e (.inl r)).1 (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) + (∑ t,
      let m := k * ((seed owner s).region.getD (e (.inr t)).1.val 0 *
        (splitWeight owner s (e (.inr t)).1 (e (.inr t)).2 +
          splitWeight owner s (e (.inr t)).1 (complement (parent_total s (e (.inr t)).1) (e (.inr t)).2)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == sourceShape owner (e (.inr t)).2)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == sourceShape owner (e (.inr t)).2)).getD (0, [], 0)).2.2)) * m
      let p : ℝ :=
        (((((seed owner s).children.find?
          (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == sourceShape owner (e (.inr t)).2)).getD
            (0, [], 0)).2.2) : ℝ) / denominator
      ((4 * N : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 )) := by
  have hD : 0 < denominator := by norm_num [denominator]
  refine mme_released_interior_child_partition_loss_bound s nB nI e q _ _
    (((2 * k : ℕ) : ℝ) * (denominator : ℝ) ^ 4) delta bound
    (by positivity) hdelta hsum ?_ ?_
  · intro r
    have h := mme_boundary_table_weight_rate_bound denominator k hD (B r) (zB r)
      (fun i w ↦ integerProfile owner s i (e (.inl r)) w) (hmu r)
      tau delta (q (e (.inl r))) htau hdelta
      (by simpa only [Nat.cast_sum, Nat.cast_mul] using
        hboundary (e (.inl r)) (zB r) (hzB r))
    convert h using 1; ring
  · intro r
    let cell := e (.inr r)
    let a := ((((seed owner s).children.find?
      (fun a => a.1 == cell.1.val && a.2.1 == sourceShape owner cell.2)).getD (0, [], 0)).2.2)
    let b := (seed owner s).region.getD cell.1.val 0
    let c := splitWeight owner s cell.1 cell.2 +
      splitWeight owner s cell.1 (complement (parent_total s cell.1) cell.2)
    have hm := mme_released_interior_child_mass_bounds owner s cell
    have ha := mme_released_interior_cell_child_parameter_bound owner s cell
    have h := mme_112_table_weight_rate_bound denominator a b c k hD ha hm.1 hm.2
      tau delta (q cell) hdelta ?_
    · simpa only [cell, a, b, c, Nat.mul_assoc] using h
    · have hi := hinterior cell (zI r) (hzI r)
      change q cell ≤ ((b : ℝ) / denominator * (c : ℝ) / denominator / 2) * _ at hi
      convert hi using 1; ring


#print axioms solution
