-- Prove2me | solution 1 for mme_released_global_interior_cells_matrix_product_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:10:00.529727+00:00
-- url     : https://prove2.me/submissions/d92330d6-30f7-429e-89bc-73afcbcfa908

import Theorems.Thm_mme_released_global_positive_cells_matrix_product_rate
import Theorems.Thm_mme_released_global_boundary_normalized_six_weight_rate

open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.CompleteSplit Filter
universe u

/-- Boundary cells are discharged by their entropy rates. Only positive
interior cells remain as extraction hypotheses in the global product. -/
theorem solution
    {K : Type u} [Field K] (owner : Fin 6)
    {parts : ℕ} (d : Fin parts ≃ Cell 8 1 (fun _ _ ↦ 8))
    (boundary : Fin parts → Bool)
    (hboundary : ∀ j, boundary j = true ↔
      0 < coarseCounts owner (d j).2 ∧ ∃ z : Fin 3, ((d j).2.val z).val = 0)
    (z : {j : Fin parts // boundary j = true} → Fin 3)
    (hz : ∀ j, ((d j.val).2.val (z j)).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : ∀ j : {j : Fin parts // boundary j = true},
        Boundary.Profile 3 (coarseCounts owner (d j.val).2),
      (∀ j i w, wordCounts owner i (d j.val).2 w = (B j).mu (z j) i w) ∧
      ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
        (reference : MME.ReleasedGlobal.Reference owner k)
        (eps : ℝ) (heps : 0 ≤ eps) (tau : ℝ) (htau : 0 ≤ tau)
        (rate : Fin parts → ℝ),
    let cell := fun j : Fin parts =>
        (source K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2))).basisAllAllowedSubtensor
          (basis K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2))) (fun i x =>
            (∀ r, grade (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (Equiv.refl _) x r) =
              ((d j).2.val i).val) ∧
            if (k * MME.ReleasedGlobal.coarseCounts owner (d j).2) = 0 then ∀ a, |(MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤ eps else
            ∀ a, |(count (fun _ : Fin ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) => Unit.unit)
                (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (Equiv.refl _) x) Unit.unit a : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ) -
              ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ)) * (MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤
                ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ)) * eps)
    let combined := fun j : Fin parts => if hj : boundary j = true then
      6 * tau * ((k : ℝ) *
          ((coarseCounts owner (d j).2 : ℝ) * Real.log 2 *
            mme_modern_entropyBits (fun w => ((B ⟨j, hj⟩).count w : ℝ) /
              (coarseCounts owner (d j).2 : ℝ)) +
            ((∑ w, (B ⟨j, hj⟩).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta)) else rate j
    (∀ j, 0 < coarseCounts owner (d j).2 →
      (∀ i : Fin 3, 0 < ((d j).2.val i).val) →
      ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
        Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
          (sixSymmetrization (cell j)) ∧
        Real.exp (rate j) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ) ^ tau) →
    ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
      Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
        (sixSymmetrization (ProfiledCW.tensor K
          ((MME.ReleasedGlobal.frame owner k hk reference).window
            (MME.ReleasedGlobal.windowGood owner k eps)))) ∧
      Real.exp (∑ j, if 0 < coarseCounts owner (d j).2 then combined j else 0) ≤
        ∑ v, ((a v * b v * c v : ℕ) : ℝ) ^ tau := by
  classical
  have h := fun j : {j : Fin parts // boundary j = true} =>
    mme_released_global_boundary_normalized_six_weight_rate.{u} owner (d j.val)
      ((hboundary j.val).mp j.property).1 (z j) (hz j) delta hdelta
  choose B hmu hrate using h
  refine ⟨B, hmu, ?_⟩
  filter_upwards [Filter.eventually_all.2 hrate] with k hkrate
  intro hk reference eps heps tau htau rate
  dsimp only
  intro hinterior
  apply mme_released_global_positive_cells_matrix_product_rate
    (K := K) owner k hk reference d eps heps tau
    (fun j => if hj : boundary j = true then
      6 * tau * ((k : ℝ) *
          ((coarseCounts owner (d j).2 : ℝ) * Real.log 2 *
            mme_modern_entropyBits (fun w => ((B ⟨j, hj⟩).count w : ℝ) /
              (coarseCounts owner (d j).2 : ℝ)) +
            ((∑ w, (B ⟨j, hj⟩).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta)) else rate j)
  intro j hjpos
  by_cases hj : boundary j = true
  · obtain ⟨M, _, hextract, hweight⟩ := hkrate ⟨j, hj⟩
    refine ⟨1, (fun _ => M), (fun _ => M), (fun _ => M), hextract eps heps K, ?_⟩
    simpa only [dif_pos hj, Fin.sum_univ_one] using hweight tau htau
  · have hi : ∀ i : Fin 3, 0 < ((d j).2.val i).val := by
      intro i
      by_contra hn
      have hz' : ((d j).2.val i).val = 0 := by omega
      exact hj ((hboundary j).mpr ⟨hjpos, i, hz'⟩)
    simpa only [dif_neg hj] using hinterior j hjpos hi


#print axioms solution
