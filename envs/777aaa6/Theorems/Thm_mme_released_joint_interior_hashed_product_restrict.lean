-- Prove2me | Theorems.Thm_mme_released_joint_interior_hashed_product_restrict
-- name    : mme_released_joint_interior_hashed_product_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:57:05.70602+00:00
-- url     : https://prove2.me/theorems/85de0005-7799-4371-8185-97012837a4a9
-- title:
--   Joint hashing composes with the owner-window product
-- statement:
--   The six exact hashing steps over the full graded joint sources compose with the released interior owner-window product. The output has exactly the product of the six post-repair copy counts and uses only whole-region mode permutations. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_interior_graded_source_product_restrict
import Theorems.Thm_mme_exact_step_permuted_product_restrict
import Theorems.Thm_mme_kronFin_repeated_isomorphic
open scoped BigOperators
open MME MME.TensorObj MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed
universe u

theorem mme_released_joint_interior_hashed_product_restrict
    {K : Type u} [Field K] (k : ℕ) (hk : 0 < k) (eps : ℝ)
    (E : ∀ r : Fin 6, ProfiledCW.ExactStep 2 (blocks r k * 4) (gradedSource r k eps)) :
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
    Restrict
      (bigAdd (fun _ : Fin (∏ r, (E r).copies) =>
        kronFin 6 (fun r => ProfiledCW.tensor K
          (fun i => (E r).output ((roleEquiv r).symm i)))))
      (kronFin 270 (fun j => ProfiledCW.tensor K (P j))) := by sorry
