-- Prove2me | solution 1 for mme_released_joint_complete_cell_product_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T22:49:56.712562+00:00
-- url     : https://prove2.me/submissions/f3ad3dff-832b-400e-82bf-4fc0c5a33809

import Theorems.Thm_mme_released_joint_interior_eventual_matrix_weight_rate
import Theorems.Thm_mme_released_joint_interior_complement_product_rate
import Theorems.Thm_mme_released_joint_interior_cells_keep_complement
import Theorems.Thm_mme_six_restricted_kron_exponential_extraction

open MME MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open MME.ReleasedJointInterior MME.RecursiveYZ.Boundary MME.RegionRate
open MME.TensorObj MME.RecursiveYZ.CWCells
open scoped BigOperators
universe u

/-- The full common-mode cell product combines pooled joint parent copies,
all interior child rates, and every complementary boundary rate. Rate
certificates and all tolerance, repair, and asymptotic losses remain explicit. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta)
    (boundaryLoss : ℝ) (hboundaryLoss : 0 < boundaryLoss)
    (eta : ℝ) (heta : 0 < eta) (loss : ℝ) (hloss : 0 < loss)
    (eps : ℝ) (heps : 0 < eps) :
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
    ∀ᶠ k : ℕ in atTop, ∀ (K : Type u) [Field K] (tau : ℝ), 0 ≤ tau →
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
      rate j = (∑ r, 6 * tau * (((2 * (k * weight j) : ℕ) : ℝ) *
            (((ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
                ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
                    ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) + (∑ t,
      let m := (k * weight j) * ((ReleasedInterior.seed (component j).1 (component j).2).region.getD (e (.inr t)).1.val 0 *
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
    let L : Fin 270 → ℕ := fun j => (2 * k) * ReleasedGlobal.coarseCounts (component j).1 (ReleasedGlobal.shapeEquiv (component j).2)
    let T : Fin 270 → TensorObj K 3 := fun j => permObj (roleEquiv (component j).1)
      ((source K 5 3 (L j)).basisAllAllowedSubtensor (basis K 5 3 (L j)) (fun i x =>
        (∀ r, grade (label 5 3 (L j) (Equiv.refl _) x r) = ((ReleasedGlobal.shapeEquiv (component j).2).val i).val) ∧
        if L j = 0 then ∀ w, |(ReleasedGlobal.profile (component j).1).2 i ⟨0,ReleasedGlobal.shapeEquiv (component j).2⟩ w| ≤ eps
        else ∀ w,
          |(count (fun _ : Fin (L j) => Unit.unit)
            (label 5 3 (L j) (Equiv.refl _) x) Unit.unit w : ℝ) / (L j : ℝ) -
            ((ReleasedGlobal.blocks (2 * k) : ℝ) / (L j : ℝ)) * (ReleasedGlobal.profile (component j).1).2 i ⟨0,ReleasedGlobal.shapeEquiv (component j).2⟩ w| ≤
            ((ReleasedGlobal.blocks (2 * k) : ℝ) / (L j : ℝ)) * eps))
    ∃ (copies : ℕ) (rows cols inner : Fin copies → ℕ), 0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (rows j) (cols j) (inner j)))
        (sixSymmetrization (TensorObj.kronFin 270 T)) ∧
      Real.exp ((6 * ((∑ r, parentRate r) * (2 * k : ℕ)) + ∑ j, rate j) +
        ∑ j, 6 * tau * ((2 * k : ℕ) * boundaryRate j)) ≤
        ∑ j, (((rows j * cols j * inner j : ℕ) : ℝ) ^ tau) := by
  classical
  intro parentRate hpositive
  obtain ⟨boundaryRate, hzeroB, hcertB, hboundary⟩ :=
    mme_released_joint_interior_complement_product_rate.{u} boundaryLoss hboundaryLoss
  refine ⟨boundaryRate, hzeroB, hcertB, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hboundary
  filter_upwards [mme_released_joint_interior_eventual_matrix_weight_rate.{u}
    delta hdelta eta heta loss hloss eps heps hpositive,
    eventually_ge_atTop N, eventually_gt_atTop 0] with k hk hkN hkpos
  intro K _ tau htau
  obtain ⟨rate, hzero, hcert, hmatrix⟩ := hk K tau htau
  refine ⟨rate, hzero, hcert, ?_⟩
  intro L T
  obtain ⟨qi, ai, bi, ci, _, hri, hwi⟩ := hmatrix
  obtain ⟨qb, ab, bb, cb, _, hrb, hwb⟩ :=
    hN (2 * k) (by omega) eps heps.le K tau htau
  exact mme_six_restricted_kron_exponential_extraction
    (mme_released_joint_interior_cells_keep_complement
      (K := K) (2 * k) (by omega) eps heps.le) tau _ _
    ⟨qi, ai, bi, ci, hri, hwi⟩ ⟨qb, ab, bb, cb, hrb, hwb⟩


#print axioms solution
