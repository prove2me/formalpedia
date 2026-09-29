-- Prove2me | Theorems.Thm_mme_released_joint_interior_eventual_matrix_weight_rate
-- name    : mme_released_joint_interior_eventual_matrix_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T22:42:35.464988+00:00
-- url     : https://prove2.me/theorems/f0cc509c-8011-444f-8378-9228302cc3c1
-- title:
--   Pooled joint entropy and complete child weights combine
-- statement:
--   Positive pooled regional surplus gives an actual matrix extraction from the released owner-window product. Its weight retains six times the summed parent rates plus the complete certified boundary and interior child rates, with explicit losses. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_hashed_matrix_weight_log_rate
import Theorems.Thm_mme_released_joint_interior_eventual_product_copy_rate
import Theorems.Thm_mme_released_joint_interior_owner_mass
open MME MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open MME.ReleasedJointInterior MME.RecursiveYZ.Boundary MME.RegionRate
open scoped BigOperators
universe u

theorem mme_released_joint_interior_eventual_matrix_weight_rate
    (delta : ℝ) (hdelta : 0 < delta)
    (eta : ℝ) (heta : 0 < eta) (loss : ℝ) (hloss : 0 < loss)
    (eps : ℝ) (heps : 0 < eps) :
    let parentRate : Fin 6 → ℝ := fun r =>
      regionalRate (parent_total r) (size r 1) (splitCount r 1) (integerProfile r 1) -
        (blocks r 1 : ℝ) * entropyModulus (Fin 2 → CompleteWord 2) eps -
        4 * eta * (blocks r 1 : ℝ) - loss
    (∀ r, 0 < parentRate r) →
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
    let P : ∀ j : Fin 270,
        ProfiledCW.Predicate (((2 * k) * weight j * denominator ^ 4) * 4) :=
      fun j i z => 0 < weight j →
        (∀ p : Fin ((2 * k) * weight j * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p q).val) =
            ReleasedInterior.parent (component j).2 0 ((roleEquiv (component j).1).symm i)) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin ((2 * k) * weight j * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p = w} : ℝ) /
              ((2 * k) * weight j * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows (component j).1 (component j).2).map
              (fun p => if ReleasedGlobal.atom p.1
                ((roleEquiv (component j).1).symm i) = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps
    ∃ (copies : ℕ) (rows cols inner : Fin copies → ℕ), 0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (rows j) (cols j) (inner j)))
        (sixSymmetrization (TensorObj.kronFin 270
          (fun j => ProfiledCW.tensor K (P j)))) ∧
      Real.exp (6 * ((∑ r, parentRate r) * (2 * k : ℕ)) + ∑ j, rate j) ≤
        ∑ j, (((rows j * cols j * inner j : ℕ) : ℝ) ^ tau) := by sorry
