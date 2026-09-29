-- Prove2me | solution 1 for mme_released_interior_112_scaled_physical_six_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:01:50.42184+00:00
-- url     : https://prove2.me/submissions/adb4f924-7775-4833-9283-bc94d5cc766a

import Theorems.Thm_mme_released_interior_112_cofinal_physical_six_extraction
import Theorems.Thm_mme_released_interior_child_scale_identities
import Mathlib.Tactic.Positivity

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
universe u

/-- Every positively weighted released 112 cell admits quantitative matrix
extractions at all sufficiently large physical replication scales. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1)
    (hweight : 0 < (seed owner s).region.getD r.val 0 *
      (splitWeight owner s r c +
        splitWeight owner s r (complement (parent_total s r) c))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      let m := k * ((seed owner s).region.getD r.val 0 *
        (splitWeight owner s r c +
          splitWeight owner s r (complement (parent_total s r) c)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
        0 < A ∧ H ≤ 4 ^ N ∧
        ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
          Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
        (Nat.choose (2 * N) N : ℝ) *
          Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ 4 * (A : ℝ) * (H : ℝ) ∧
        ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b d : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
            (sixSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount owner s r c +
                  splitCount owner s r (complement (parent_total s r) c))) (Equiv.refl _)
                (fun _ => Unit.unit) (fun _ i => (c.val i).val)
                (fun i _ w => (2 * k) * integerProfile owner s i ⟨r, c⟩ w))) ∧
          ((A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
            Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))))) ^ 2 ≤ (copies : ℝ) ∧
          ∀ j, a j * b j * d j = 5 ^ (6 * (4 * G + 2 * L)) := by
  let scale := (seed owner s).region.getD r.val 0 *
    (splitWeight owner s r c +
      splitWeight owner s r (complement (parent_total s r) c)) * denominator
  have hscale : 0 < scale := Nat.mul_pos hweight (by decide)
  obtain ⟨C, hC, hlarge⟩ :=
    mme_released_interior_112_cofinal_physical_six_extraction owner s r c z hshape
  obtain ⟨M, hM⟩ := eventually_atTop.1 hlarge
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop M] with k hk
  have hkm : M ≤ k * scale := hk.trans (Nat.le_mul_of_pos_right k hscale)
  obtain ⟨A, H, family, hApos, hH, hA, hAH, hextract⟩ := hM (k * scale) hkm
  refine ⟨A, H, family, hApos, hH, hA, hAH, ?_⟩
  intro K _
  obtain ⟨copies, a, b, d, hcopies, hrestrict, hcount, hvolume⟩ := hextract K
  refine ⟨copies, a, b, d, hcopies, ?_, hcount, hvolume⟩
  obtain ⟨hlength, hprofile⟩ := mme_released_interior_child_scale_identities owner s r c k
  dsimp only [scale] at hrestrict
  simp only [hprofile] at hrestrict
  have htensor := congrArg (fun n : ℕ => sixSymmetrization
    (CWCells.unbroken K 5 2 n (Equiv.refl _)
      (fun _ => Unit.unit) (fun _ i => (c.val i).val)
      (fun i _ w => (2 * k) * integerProfile owner s i ⟨r, c⟩ w))) hlength
  exact (congrArg (fun T => TensorObj.Restrict
    (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j))) T) htensor).mp hrestrict


#print axioms solution
