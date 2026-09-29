-- Prove2me | solution 1 for mme_released_interior_112_physical_six_entropy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:09:33.041583+00:00
-- url     : https://prove2.me/submissions/a217b2d2-bf28-4a23-94f5-662795613002

import Theorems.Thm_mme_released_interior_112_scaled_physical_six_extraction
import Theorems.Thm_mme_released_interior_child_parameter_bound
import Theorems.Thm_mme_112_squared_extraction_entropy_rate

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
universe u

/-- Every positively weighted released 112 child attains its entropy copy
rate on its actual physical tensor, including zero outer parameters. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1)
    (hweight : 0 < (seed owner s).region.getD r.val 0 *
      (splitWeight owner s r c +
        splitWeight owner s r (complement (parent_total s r) c)))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop,
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
  let p : ℕ := (((seed owner s).children.find?
    (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
  let l := 2 * p
  let g := denominator - l
  let scale := (seed owner s).region.getD r.val 0 *
    (splitWeight owner s r c +
      splitWeight owner s r (complement (parent_total s r) c)) * denominator
  have hpbound : p ≤ denominator / 2 :=
    mme_released_interior_child_parameter_bound owner s r (sourceShape owner c)
  have hsum : l + g = denominator := by
    dsimp [l, g]
    omega
  have hD : 0 < l + g := by rw [hsum]; decide
  have hscale : 0 < scale := Nat.mul_pos hweight (by decide)
  have hp : (l : ℝ) / (2 * (denominator : ℝ)) = (p : ℝ) / denominator := by
    dsimp [l]
    push_cast
    ring
  obtain ⟨C, _, hextract⟩ :=
    mme_released_interior_112_scaled_physical_six_extraction owner s r c z hshape hweight
  have hrate := mme_112_squared_extraction_entropy_rate l g hD C delta hdelta
  simp only [hsum, hp] at hrate
  obtain ⟨M, hM⟩ := eventually_atTop.1 hrate
  filter_upwards [hextract, eventually_ge_atTop M] with k hk hlarge
  have hkm : M ≤ k * scale := hlarge.trans (Nat.le_mul_of_pos_right k hscale)
  obtain ⟨A, H, family, hApos, hH, hA, hAH, hmat⟩ := hk
  have hlog := hM (k * scale) hkm A H
  dsimp only at hlog ⊢
  intro K _
  obtain ⟨copies, a, b, d, hcopies, hrestrict, hcount, hvolume⟩ := hmat K
  refine ⟨copies, a, b, d, hcopies, hrestrict, hvolume, ?_⟩
  exact hlog copies hApos family.hHpos hH hA hAH hcount


#print axioms solution
