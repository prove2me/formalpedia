-- Prove2me | solution 1 for mme_released_interior_112_all_cells_physical_entropy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:24:43.363712+00:00
-- url     : https://prove2.me/submissions/5216adf8-7a36-4f74-ad0d-8f0d10380376

import Theorems.Thm_mme_released_interior_112_simultaneous_physical_entropy_rate
import Theorems.Thm_mme_released_interior_empty_cell_six_extraction

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
universe u

/-- All released 112 cells attain the entropy copy rate at common physical
scales. Empty cells contribute one scalar copy and zero logarithmic rate. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (owner : Fin 6) (s : Fin 45) (r : Fin 6)
      (c : Split s) (z : Fin 3),
      (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
      let m := k * ((seed owner s).region.getD r.val 0 *
        (splitWeight owner s r c +
          splitWeight owner s r (complement (parent_total s r) c)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      let p : ℝ :=
        (((((seed owner s).children.find?
          (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD
            (0, [], 0)).2.2) : ℝ) / denominator
      ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b d : Fin copies → ℕ),
        0 < copies ∧
        TensorObj.Restrict (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
          (sixSymmetrization
            (CWCells.unbroken K 5 2
              ((2 * k) * (splitCount owner s r c +
                splitCount owner s r (complement (parent_total s r) c))) (Equiv.refl _)
              (fun _ => Unit.unit) (fun _ i => (c.val i).val)
              (fun i _ w => (2 * k) * integerProfile owner s i ⟨r, c⟩ w))) ∧
        (∀ j, a j * b j * d j = 5 ^ (6 * (4 * G + 2 * L))) ∧
        ((4 * N : ℕ) : ℝ) *
          (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) ≤
            Real.log (copies : ℝ) := by
  filter_upwards [mme_released_interior_112_simultaneous_physical_entropy_rate
    delta hdelta] with k hk
  intro owner s r c z hshape
  by_cases hweight : 0 < (seed owner s).region.getD r.val 0 *
    (splitWeight owner s r c +
      splitWeight owner s r (complement (parent_total s r) c))
  · exact hk owner s r c z hshape hweight
  · have hzero := Nat.eq_zero_of_not_pos hweight
    dsimp only
    simp only [hzero, Nat.mul_zero, zero_add, Nat.pow_zero,
      Nat.cast_zero, zero_mul]
    intro K _
    refine ⟨1, (fun _ => 1), (fun _ => 1), (fun _ => 1), by decide, ?_, ?_, ?_⟩
    · exact mme_released_interior_empty_cell_six_extraction owner s r c k hzero
    · simp
    · simp


#print axioms solution
