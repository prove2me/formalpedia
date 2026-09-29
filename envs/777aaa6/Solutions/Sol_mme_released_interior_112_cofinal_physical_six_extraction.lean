-- Prove2me | solution 1 for mme_released_interior_112_cofinal_physical_six_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:55:28.511287+00:00
-- url     : https://prove2.me/submissions/50311702-7295-4967-88e0-9ebbdb0f1a5f

import Theorems.Thm_mme_released_interior_112_cofinal_canonical_matrix_extraction
import Theorems.Thm_mme_released_interior_112_six_canonical_physical_iso
import Theorems.Thm_mme_cyclic_uniform_extraction_six_count
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
universe u

/-- Every physical released 112 child has cofinal full-symmetrization
matrix extractions with explicit positive copy and volume bounds. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop,
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
        ∀ (K : Type u) [Field K], ∃ (k : ℕ) (a b d : Fin k → ℕ),
          0 < k ∧
          TensorObj.Restrict (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
            (sixSymmetrization
              (CWCells.unbroken K 5 2 (2 * N) (Equiv.refl _)
                (fun _ => Unit.unit) (fun _ i => (c.val i).val)
                (fun i _ w => 2 * m * childMarginal owner s r c i w))) ∧
          ((A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
            Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))))) ^ 2 ≤ (k : ℝ) ∧
          ∀ j, a j * b j * d j = 5 ^ (6 * (4 * G + 2 * L)) := by
  obtain ⟨C, hC, hfamilies⟩ :=
    mme_released_interior_112_cofinal_canonical_matrix_extraction owner s r c z hshape
  refine ⟨C, hC, ?_⟩
  apply hfamilies.mono
  intro m hm
  obtain ⟨A, H, family, hApos, hH, hA, hAH, hextract⟩ := hm
  refine ⟨A, H, family, hApos, hH, hA, hAH, ?_⟩
  intro K _
  obtain ⟨k, a, b, d, hk, hrestrict, hcount, hvolume⟩ := hextract K
  obtain ⟨copies, a', b', d', hcopies, hrestrict', hcount', hvolume'⟩ :=
    mme_cyclic_uniform_extraction_six_count a b d hk hrestrict hvolume _
      (by positivity) hcount
  have hiso := mme_released_interior_112_six_canonical_physical_iso
    owner s r c z hshape (2 * (denominator * m)) (2 * m) K
  refine ⟨copies, a', b', d', hcopies, hrestrict'.trans hiso.1, hcount', ?_⟩
  intro j
  have hpow (n : ℕ) : ((5 ^ n) ^ 3) ^ 2 = 5 ^ (6 * n) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  exact (hvolume' j).trans (hpow _)


#print axioms solution
