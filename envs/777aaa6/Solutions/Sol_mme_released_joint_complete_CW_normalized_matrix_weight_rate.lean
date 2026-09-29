-- Prove2me | solution 1 for mme_released_joint_complete_CW_normalized_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T22:58:32.403283+00:00
-- url     : https://prove2.me/submissions/10648f15-a0ae-434e-aa6c-337223433e7f

import Theorems.Thm_mme_released_joint_outer_windows_matrix_weight_rate
import Theorems.Thm_mme_released_joint_outer_CW_normalized_matrix_weight_rate

open MME MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open MME.ReleasedJointInterior MME.RecursiveYZ.Boundary MME.RegionRate
open MME.TensorObj
open scoped BigOperators
universe u

/-- The actual outer extraction and complete pooled window rate yield matrix
families in CW powers. All rate certificates and losses remain explicit, and
source multiplicity factors out exactly. -/
theorem solution
    {K : Type u} [Field K]
    (delta : ℝ) (hdelta : 0 < delta)
    (boundaryLoss : ℝ) (hboundaryLoss : 0 < boundaryLoss)
    (eta : ℝ) (heta : 0 < eta) (loss : ℝ) (hloss : 0 < loss)
    (rho : Fin 6 → ℝ) (hrho : ∀ owner, 0 ≤ rho owner)
    (hgap : ∀ owner, rho owner < (ReleasedGlobal.profile owner).rate (fun _ ↦ 1)) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    let parentRate : Fin 6 → ℝ := fun r =>
      regionalRate (parent_total r) (size r 1) (splitCount r 1) (integerProfile r 1) -
        (blocks r 1 : ℝ) * entropyModulus (Fin 2 → CompleteWord 2) eps -
        4 * eta * (blocks r 1 : ℝ) - loss
    (∀ r, 0 < parentRate r) →
    ∃ boundaryRate : Fin 270 → ℝ,
      (∀ j, (0 < weight j ∨ ReleasedGlobal.coarseCounts (component j).1 (ReleasedGlobal.shapeEquiv (component j).2) = 0) → boundaryRate j = 0) ∧
      (∀ j, ¬ 0 < weight j → 0 < ReleasedGlobal.coarseCounts (component j).1 (ReleasedGlobal.shapeEquiv (component j).2) →
        ∃ (z : Fin 3) (B : Boundary.Profile 3 (ReleasedGlobal.coarseCounts (component j).1 (ReleasedGlobal.shapeEquiv (component j).2))),
          ((ReleasedGlobal.shapeEquiv (component j).2).val z).val = 0 ∧
          (∀ i w, ReleasedGlobal.wordCounts (component j).1 i (ReleasedGlobal.shapeEquiv (component j).2) w = B.mu z i w) ∧
          boundaryRate j = (ReleasedGlobal.coarseCounts (component j).1 (ReleasedGlobal.shapeEquiv (component j).2) : ℝ) * Real.log 2 *
            mme_modern_entropyBits (fun w => (B.count w : ℝ) /
              (ReleasedGlobal.coarseCounts (component j).1 (ReleasedGlobal.shapeEquiv (component j).2) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - boundaryLoss) ∧
    ∀ᶠ n : ℕ in atTop, ∀ (tau : ℝ), 0 ≤ tau →
    ∃ rate : Fin 270 → ℝ,
      (∀ j, weight j = 0 → rate j = 0) ∧
      (∀ j, 0 < weight j →
      ∃ (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (ReleasedInterior.parent (component j).2))
        (zB : Fin nB → Fin 3) (zI : Fin nI → Fin 3),
        (∀ j, ((e (.inl j)).2.val (zB j)).val = 0) ∧
        (∀ j i, ((e (.inr j)).2.val i).val = if i = zI j then 2 else 1) ∧
    ∃ B : ∀ r, Boundary.Profile 2
        (ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
          ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2)),
      (∀ r i w, ReleasedInterior.integerProfile (component j).1 (component j).2 i (e (.inl r)) w = (B r).mu (zB r) i w) ∧
      rate j = (∑ r, 6 * tau * (((2 * ((2 * n ^ 2) * weight j) : ℕ) : ℝ) *
            (((ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
                ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
                    ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) + (∑ t,
      let m := ((2 * n ^ 2) * weight j) * ((ReleasedInterior.seed (component j).1 (component j).2).region.getD (e (.inr t)).1.val 0 *
        (ReleasedInterior.splitWeight (component j).1 (component j).2 (e (.inr t)).1 (e (.inr t)).2 +
          ReleasedInterior.splitWeight (component j).1 (component j).2 (e (.inr t)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inr t)).1) (e (.inr t)).2)) * denominator)
      let N := denominator * m
      let L := (2 * ((((ReleasedInterior.seed (component j).1 (component j).2).children.find?
        (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == ReleasedInterior.sourceShape (component j).1 (e (.inr t)).2)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((ReleasedInterior.seed (component j).1 (component j).2).children.find?
        (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == ReleasedInterior.sourceShape (component j).1 (e (.inr t)).2)).getD (0, [], 0)).2.2)) * m
      let p : ℝ :=
        (((((ReleasedInterior.seed (component j).1 (component j).2).children.find?
          (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == ReleasedInterior.sourceShape (component j).1 (e (.inr t)).2)).getD
            (0, [], 0)).2.2) : ℝ) / denominator
      ((4 * N : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 )) ∧
    ∃ (inputs : Fin 6 → ℕ) (copies : ℕ) (rows cols inner : Fin copies → ℕ),
      (∀ owner, 1 ≤ inputs owner) ∧
      (∀ owner, inputs owner ≤ (ReleasedGlobal.blocks ((2 * n) ^ 2) + 1) ^ 10935) ∧
      0 < copies ∧
      Restrict (bigAdd (fun j => MMObj K (rows j) (cols j) (inner j)))
        (bigAdd (fun _ : Fin (∏ owner, inputs owner ^ 6) =>
          (CWObj K 5).kronPow (144 * ReleasedGlobal.blocks ((2 * n) ^ 2)))) ∧
      ((∏ owner, inputs owner ^ 6 : ℕ) : ℝ) *
        Real.exp (6 * (∑ owner, rho owner * (ReleasedGlobal.blocks ((2 * n) ^ 2) : ℝ)) +
          ((6 * ((∑ r, parentRate r) * ((2 * n) ^ 2 : ℕ)) + ∑ j, rate j) +
            ∑ j, 6 * tau * (((2 * n) ^ 2 : ℕ) * boundaryRate j))) ≤
          ∑ j, (((rows j * cols j * inner j : ℕ) : ℝ) ^ tau) := by
  classical
  obtain ⟨eps0, heps0, k0, houter⟩ :=
    mme_released_joint_outer_CW_normalized_matrix_weight_rate (K := K) rho hrho hgap
  refine ⟨eps0, heps0, ?_⟩
  intro eps heps hepsbound parentRate hpositive
  obtain ⟨boundaryRate, hzeroB, hcertB, hwindow⟩ :=
    mme_released_joint_outer_windows_matrix_weight_rate.{u}
      delta hdelta boundaryLoss hboundaryLoss eta heta loss hloss eps heps hpositive
  refine ⟨boundaryRate, hzeroB, hcertB, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hwindow
  filter_upwards [eventually_ge_atTop (max k0 (max N 1))] with n hn
  intro tau htau
  have hnN : N ≤ n := (le_max_left N 1).trans ((le_max_right k0 _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right N 1).trans ((le_max_right k0 _).trans hn)
  have hn0 : k0 ≤ n := (le_max_left k0 _).trans hn
  have hlarge : N ≤ 2 * n ^ 2 := by nlinarith
  obtain ⟨rate, hzero, hcert, hmatrix⟩ := hN (2 * n ^ 2) hlarge K tau htau
  refine ⟨rate, hzero, hcert, ?_⟩
  have hscale : 2 * (2 * n ^ 2) = (2 * n) ^ 2 := by ring
  rw [hscale] at hmatrix
  exact houter eps heps hepsbound (2 * n) (by omega) tau
    ((6 * ((∑ r, parentRate r) * ((2 * n) ^ 2 : ℕ)) + ∑ j, rate j) +
      ∑ j, 6 * tau * (((2 * n) ^ 2 : ℕ) * boundaryRate j)) hmatrix


#print axioms solution
