-- Prove2me | Theorems.Thm_mme_released_joint_interior_hashed_owner_output_restrict
-- name    : mme_released_joint_interior_hashed_owner_output_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T16:26:24.341475+00:00
-- url     : https://prove2.me/theorems/ab772135-0b3c-4cee-8a3c-d40a7c044157
-- title:
--   Joint hashing yields repeated exact owner outputs
-- statement:
--   Joint parent hashing followed by physical owner regrouping restricts the released owner-window product to exact owner outputs with precisely the product of the six post-repair copy counts. The exact output identities of the hashing steps are explicit hypotheses supplied by the existing step construction. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_released_joint_interior_hashed_product_restrict
import Theorems.Thm_mme_released_joint_interior_owner_output_product_restrict
open scoped BigOperators
open MME MME.TensorObj MME.RecursiveYZ MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed
universe u

theorem mme_released_joint_interior_hashed_owner_output_restrict
    {K : Type u} [Field K] (k : ℕ) (hk : 0 < k) (eps : ℝ)
    (E : ∀ r : Fin 6, ProfiledCW.ExactStep 2 (blocks r k * 4) (gradedSource r k eps))
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    (houtput : ∀ r, (E r).output = fun i x =>
      Graded (parent_total r) i (a r)
        (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
      Useful (fullCell (parent_total r) (a r)) (integerProfile r k i)
        (ProfiledCW.split (positions r k) (positions_length r k) x))
    (e : ∀ j : Fin 270, Fin ((k * weight j * denominator ^ 4) * 2) ≃
      Position (fun r => size r k j))
    (length : ∀ j : Fin 270,
      ((k * weight j * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
        (k * weight j * denominator ^ 4) * 4) :
    let P : ∀ j : Fin 270,
        ProfiledCW.Predicate ((k * weight j * denominator ^ 4) * 4) :=
      fun j i z => 0 < weight j →
        (∀ p : Fin (k * weight j * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p q).val) =
            ReleasedInterior.parent (component j).2 0 ((roleEquiv (component j).1).symm i)) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * weight j * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p = w} : ℝ) /
              (k * weight j * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows (component j).1 (component j).2).map
              (fun p => if ReleasedGlobal.atom p.1
                ((roleEquiv (component j).1).symm i) = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps
    let O : ∀ j : Fin 270,
        ProfiledCW.Predicate ((k * weight j * denominator ^ 4) * 4) :=
      fun j i x =>
        Graded (ReleasedInterior.parent_total (component j).2)
          ((roleEquiv (component j).1).symm i)
          (fun r t => (splitEquiv r j).symm (a r j t))
          (ProfiledCW.split (e j) (length j) x) ∧
        Useful (fullCell (ReleasedInterior.parent_total (component j).2)
          (fun r t => (splitEquiv r j).symm (a r j t)))
          (fun c w => k * weight j * ReleasedInterior.integerProfile
            (component j).1 (component j).2 ((roleEquiv (component j).1).symm i) c w)
          (ProfiledCW.split (e j) (length j) x)
    Restrict
      (bigAdd (fun _ : Fin (∏ r, (E r).copies) =>
        kronFin 270 (fun j => ProfiledCW.tensor K (O j))))
      (kronFin 270 (fun j => ProfiledCW.tensor K (P j))) := by sorry
