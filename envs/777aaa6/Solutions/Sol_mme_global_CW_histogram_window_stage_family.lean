-- Prove2me | solution 1 for mme_global_CW_histogram_window_stage_family
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T10:27:13.740774+00:00
-- url     : https://prove2.me/submissions/dc3a9870-53ec-4bb2-8101-ddd66e557aff

import Definitions.Def_mme_global_CW_histogram_frame
import Theorems.Thm_mme_global_CW_supported_histogram_admissibility
import Theorems.Thm_mme_prescribed_histogram_polynomial_type_cover
open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.GlobalCW MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem solution {ell M : ℕ} (D : HistogramFrame ell M)
    (good : Fin 3 → (Cell D.degree D.R D.bounds → CompleteWord ell → ℕ) → Prop)
    (d : ℕ) (hd : 1 < d) :
    ∃ (types : ℕ) (profiles : Fin types → D.AdmissibleProfile),
      types ≤ (D.L + 1) ^ (3 * Fintype.card (Cell D.degree D.R D.bounds) *
        Fintype.card (CompleteWord ell)) ∧
      (∀ j i, good i ((profiles j).val i)) ∧
      (∀ j i x, (D.stage (profiles j) d hd).output i x → D.window good i x) ∧
      (∀ x : Fin 3 → FineWord M, supported x → (∀ i, D.window good i (x i)) →
        ∃! j, ∀ i, (D.stage (profiles j) d hd).output i (x i)) := by
  classical
  let supp (x : Fin 3 → Place D.n → CompleteWord ell) : Prop :=
    ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2
  obtain ⟨types,mu,hpoly,hwitness,hinside,hcover⟩ :=
    mme_prescribed_histogram_polynomial_type_cover (cell D.reference) supp
      (fun i f ↦ Graded i D.reference f) good
  have hadmissible (j : Fin types) : D.Admissible (mu j) := by
    obtain ⟨x,hs,hx⟩ := hwitness j
    have hu : (fun i ↦ count (cell D.reference) (x i)) = mu j :=
      funext fun i ↦ funext fun c ↦ funext fun w ↦ (hx i).2.2 c w
    have hh := mme_global_CW_supported_histogram_admissibility D x (fun i ↦ (hx i).1) hs
    rwa [hu] at hh
  let profiles (j : Fin types) : D.AdmissibleProfile := ⟨mu j,hadmissible j⟩
  have hcard : Fintype.card (Place D.n) = D.L := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr D.positions).symm
  refine ⟨types,profiles,?_,?_,?_,?_⟩
  · simpa only [hcard] using hpoly
  · intro j i
    obtain ⟨x,hs,hx⟩ := hwitness j
    exact (hx i).2.1
  · intro j i x hx
    exact hinside j i (split D.positions D.length x) hx
  · intro x hs hx
    exact hcover (fun i ↦ split D.positions D.length (x i))
      (fun p r ↦ hs (Fin.cast D.length (finProdFinEquiv (D.positions.symm p,r)))) hx
