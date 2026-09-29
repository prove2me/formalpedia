-- Prove2me | solution 1 for mme_released_global_parent_source_restricts_common_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:10:37.664023+00:00
-- url     : https://prove2.me/submissions/007c4c74-a3ca-4b70-8cca-748baad86076

import Theorems.Thm_mme_released_global_normalized_cell_eq_parent_source
import Theorems.Thm_mme_basis_all_allowed_subtensor_mono

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
universe u

private theorem alpha_le_denominator : ∀ (owner : Fin 6) (s : Fin 45),
    alpha owner s ≤ denominator := by decide +kernel

/-- The local parent source restricts from its normalized global cell at the
same histogram tolerance. The released coarse weight is at most the denominator,
so the exact bridge's smaller tolerance is contained in the common window. -/
theorem solution
    {K : Type u} [Field K] (owner : Fin 6) (s : Fin 45)
    (ha0 : 0 < alpha owner s) (t : ℕ) (ht : 0 < t) (eps : ℝ) (heps : 0 ≤ eps) :
    let L := t * coarseCounts owner (shapeEquiv s)
    TensorObj.Restrict
      (ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord (L * 4)) =>
      (∀ p : Fin L,
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) =
          ((shapeEquiv s).val i).val) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin L //
          ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) / L -
          ((((jointRows owner s).map
            (fun a => if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ)^4| ≤ eps))
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L)
      (fun i x =>
        (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = ((shapeEquiv s).val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / L -
          ((blocks t : ℝ) / L) * (profile owner).2 i ⟨0,shapeEquiv s⟩ w| ≤
          ((blocks t : ℝ) / L) * (eps))) := by
  classical
  dsimp only
  rw [← mme_released_global_normalized_cell_eq_parent_source owner s ha0 t ht eps]
  apply mme_basis_all_allowed_subtensor_mono
  intro i x hx
  have ha : (alpha owner s : ℝ) ≤ denominator := by
    exact_mod_cast alpha_le_denominator owner s
  have hd : (0 : ℝ) < denominator := by norm_num [denominator]
  have htol : (alpha owner s : ℝ) / denominator * eps ≤ eps := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ((div_le_one hd).mpr ha) heps
  refine ⟨hx.1, ?_⟩
  split_ifs at hx ⊢ with hz
  · intro w
    exact (hx.2 w).trans htol
  · intro w
    exact (hx.2 w).trans (mul_le_mul_of_nonneg_left htol (by positivity))


#print axioms solution
