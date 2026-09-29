-- Prove2me | solution 1 for mme_released_interior_112_cofinal_canonical_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:47:45.876344+00:00
-- url     : https://prove2.me/submissions/9982777d-4faa-433b-8fe1-fc5e752aaf30

import Theorems.Thm_mme_released_interior_112_intact_family_certificate
import Theorems.Thm_mme_released_interior_112_cofinal_induced_families
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Mathlib.Tactic.FinCases

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
universe u

private theorem source_shape_112 (owner : Fin 6) {s : Fin 45}
    (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    sourceShape owner c = List.ofFn (fun i : Fin 3 => if i = role owner z then 2 else 1) := by
  unfold sourceShape
  congr 1
  funext i
  rw [hshape]
  have heq : inverseRole owner i = z ↔ i = role owner z := by
    fin_cases owner <;> fin_cases z <;> fin_cases i <;> decide
  simp only [heq]

/-- Exact canonical child tensors have cofinal matrix extractions with
positive copy counts, both directional estimates and an explicit volume. -/
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
            (cyclicSymmetrization
              (CWCells.unbroken K 5 2 (2 * N) (Equiv.refl _)
                (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => 2 * m * childMarginal owner s r c (Equiv.swap z 2 i) w))) ∧
          (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
            Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) ≤ (k : ℝ) ∧
          ∀ j, a j * b j * d j = (5 ^ (4 * G + 2 * L)) ^ 3 := by
  dsimp only
  have hs : sourceShape owner c = [1, 1, 2] ∨
      sourceShape owner c = [1, 2, 1] ∨ sourceShape owner c = [2, 1, 1] := by
    rw [source_shape_112 owner c z hshape]
    have hv : ∀ v : Fin 3,
        List.ofFn (fun i : Fin 3 => if i = v then 2 else 1) = [1, 1, 2] ∨
        List.ofFn (fun i : Fin 3 => if i = v then 2 else 1) = [1, 2, 1] ∨
        List.ofFn (fun i : Fin 3 => if i = v then 2 else 1) = [2, 1, 1] := by decide
    exact hv (role owner z)
  obtain ⟨C, hC, hfamilies⟩ :=
    mme_released_interior_112_cofinal_induced_families owner s r (sourceShape owner c) hs
  refine ⟨C, hC, ?_⟩
  apply hfamilies.mono
  intro m hm
  obtain ⟨A, H, family, hApos, hH, hA, hAH⟩ := hm
  refine ⟨A, H, family, hApos, hH, hA, hAH, ?_⟩
  intro K _
  obtain ⟨certificate⟩ := mme_released_interior_112_intact_family_certificate
    owner s r c z hshape m A H K family
  obtain ⟨k, a, b, d, hrestrict, hcount, hvolume⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction certificate family.hHpos
  have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
  have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
  have hpositive : 0 < (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) := by positivity
  have hk : 0 < k := by exact_mod_cast hpositive.trans_le hcount
  exact ⟨k, a, b, d, hk, hrestrict, hcount, hvolume⟩


#print axioms solution
