-- Prove2me | solution 1 for mme_regional_tolerance_window_step_family
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T21:21:38.056467+00:00
-- url     : https://prove2.me/submissions/08deb303-0e4b-483f-828c-b099e373d0d8

import Definitions.Def_mme_regional_tolerance_window_data
import Theorems.Thm_mme_regional_parent_mixture_lipschitz
import Theorems.Thm_mme_regional_supported_histogram_admissibility
import Theorems.Thm_mme_prescribed_histogram_polynomial_type_cover
import Theorems.Thm_mme_regional_target_marginals
open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem solution {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (delta eps rate : ℝ) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤ (D.minimum : ℝ) * eps^2)
    (hbudget : ∀ mu : WindowProfile D, WindowAdmissible D mu →
      (∀ i, WindowClose D delta i (mu i)) → rate ≤ windowLogBudget D mu eps) :
    ∃ (types : ℕ) (steps : Fin types → IntegerStep ell M (parentWindow D (eps+2*delta))),
      types ≤ (Fintype.card (Position D.n) + 1) ^
        (3 * Fintype.card (Cell D.half D.R D.parent) * Fintype.card (CompleteWord ell)) ∧
      (∀ j, rate ≤ (steps j).certifiedLogCopies) ∧
      (∀ j i x, (steps j).output i x → childWindow D delta i x) ∧
      (∀ x : Fin 3 → FineWord M, supported x → (∀ i, childWindow D delta i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i)) := by
  classical
  let supp (x : Fin 3 → Position D.n → CompleteWord ell) : Prop :=
    ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2
  obtain ⟨types,mu,hpoly,hwitness,hinside,hcover⟩ :=
    mme_prescribed_histogram_polynomial_type_cover (fullCell D.total D.reference) supp
      (fun i f ↦ Graded D.total i D.reference f) (WindowClose D delta)
  have hadmissible (j : Fin types) : WindowAdmissible D (mu j) := by
    obtain ⟨x,hs,hx⟩ := hwitness j
    have hu : (fun i ↦ count (fullCell D.total D.reference) (x i)) = mu j :=
      funext fun i ↦ funext fun c ↦ funext fun w ↦ (hx i).2.2 c w
    have hh := mme_regional_supported_histogram_admissibility D x (fun i ↦ (hx i).1) hs
    change WindowAdmissible D (fun i ↦ count (fullCell D.total D.reference) (x i)) at hh
    rwa [hu] at hh
  have hclose (j : Fin types) : ∀ i, WindowClose D delta i (mu j i) := by
    obtain ⟨x,hs,hx⟩ := hwitness j
    exact fun i ↦ (hx i).2.1
  have hmass := (mme_regional_target_marginals D.m 0 D.reference D.reference_target).1
  let steps (j : Fin types) : IntegerStep ell M (parentWindow D (eps+2*delta)) := {
    half := D.half, R := D.R, parent := D.parent, n := D.n, total := D.total,
    half_eq := D.half_eq, m := D.m, N := D.N, hashPositions := D.hashPositions,
    L := D.L, positions := D.positions, length := D.length, mu := mu j,
    mass := (hadmissible j).1, support := (hadmissible j).2.1,
    boundary := (hadmissible j).2.2, reference := D.reference,
    reference_target := D.reference_target, minimum := D.minimum, repairScale := D.repairScale,
    minimum_pos := D.minimum_pos, repairScale_gt_one := D.repairScale_gt_one,
    parent_size := D.parent_size, split_divisible := D.split_divisible,
    epsilon := eps, epsilon_pos := heps, size_test := hsize,
    source_inside := fun i x hx ↦
      (mme_regional_parent_mixture_lipschitz D.total D.n D.m hmass (mu j i) (D.mu i)
        delta hdelta (hclose j i)).2 eps (split D.positions D.length x) hx }
  refine ⟨types,steps,hpoly,?_,?_,?_⟩
  · intro j
    exact hbudget (mu j) (hadmissible j) (hclose j)
  · intro j i x hx
    exact hinside j i (split D.positions D.length x) hx
  · intro x hs hx
    exact hcover (fun i ↦ split D.positions D.length (x i))
      (fun p r ↦ hs (Fin.cast D.length (finProdFinEquiv (D.positions.symm p,r)))) hx
