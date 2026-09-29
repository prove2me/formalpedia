-- Prove2me | solution 1 for mme_released_global_exact_histogram_window_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T02:59:30.429987+00:00
-- url     : https://prove2.me/submissions/1eccdfc7-5fd8-489a-a56c-c380233271c0

import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_basis_projected_family_restrict

open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u

private theorem released_normalized_center (owner : Fin 6) (k L : ℕ)
    (i : Fin 3) (c : Cell 8 1 (fun _ _ ↦ 8)) (w : Word) :
    ((k * wordCounts owner i c.2 w : ℕ) : ℝ) / L =
      ((blocks k : ℝ) / L) * (profile owner).2 i c w := by
  change ((k * wordCounts owner i c.2 w : ℕ) : ℝ) / L =
    ((denominator ^ 5 * k : ℕ) : ℝ) / L *
      ((wordCounts owner i c.2 w : ℝ) / (denominator : ℝ)^5)
  have halg (d n m t : ℝ) (hd : d ≠ 0) :
      n * m / t = (d^5 * n / t) * (m / d^5) := by
    field_simp
  simp only [Nat.cast_mul, Nat.cast_pow]
  exact halg _ _ _ _ (by norm_num [denominator])

private theorem exact_histogram_window_restriction
    {K : Type u} [Field K] (L : ℕ) (hL : 0 < L)
    (shape : Fin 3 → ℕ) (mu : Fin 3 → Word → ℕ)
    (center : Fin 3 → Word → ℝ) (total eps : ℝ)
    (htotal : 0 ≤ total) (heps : 0 ≤ eps)
    (hcenter : ∀ i w, (mu i w : ℝ) / L = (total / L) * center i w) :
    Restrict
      (unbroken K 5 3 L (Equiv.refl _) (fun _ => Unit.unit)
        (fun _ => shape) (fun i _ => mu i))
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
        (∀ r, CWCells.grade (label 5 3 L (Equiv.refl _) x r) = shape i) ∧
        if L = 0 then ∀ w, |center i w| ≤ eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
          (total / L) * center i w| ≤ (total / L) * eps)) := by
  classical
  apply mme_basis_projected_family_restrict (source K 5 3 L) (basis K 5 3 L) _
    (fun (_ : Fin 1) => allowed 5 3 L (Equiv.refl _) (fun _ => Unit.unit)
      (fun _ => shape) (fun i _ => mu i))
  · intro j i x hx
    refine ⟨hx.1, ?_⟩
    rw [if_neg (Nat.ne_of_gt hL)]
    intro w
    have hc := hx.2 Unit.unit w
    rw [hc, hcenter, sub_self, abs_zero]
    exact mul_nonneg (div_nonneg htotal (Nat.cast_nonneg _)) heps
  · intro x js _ _
    exact ⟨0, funext (fun i => Fin.eq_zero (js i))⟩

/-- Exact released histograms lie in every nonnegative normalized cell window. -/
theorem solution
    {K : Type u} [Field K] (owner : Fin 6) (k : ℕ)
    (c : Cell 8 1 (fun _ _ ↦ 8)) (hL : 0 < k * coarseCounts owner c.2)
    (eps : ℝ) (heps : 0 ≤ eps) :
    let L := k * coarseCounts owner c.2
    Restrict
      (unbroken K 5 3 L (Equiv.refl _) (fun _ => Unit.unit)
        (fun _ i => (c.2.val i).val) (fun i _ w => k * wordCounts owner i c.2 w))
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
        (∀ r, CWCells.grade (label 5 3 L (Equiv.refl _) x r) = (c.2.val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i c w| ≤ eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
          ((blocks k : ℝ) / (L : ℝ)) * (profile owner).2 i c w| ≤
          ((blocks k : ℝ) / (L : ℝ)) * eps)) := by
  exact exact_histogram_window_restriction _ hL _ _ _ _ _
    (Nat.cast_nonneg _) heps (released_normalized_center owner k _ · c ·)


#print axioms solution
