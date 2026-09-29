-- Prove2me | solution 1 for mme_released_joint_interior_graded_source_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:35:14.824892+00:00
-- url     : https://prove2.me/submissions/0acdbed4-c9af-43da-929c-4c33d43af814

import Definitions.Def_mme_released_joint_interior_graded_source
import Theorems.Thm_mme_released_joint_interior_common_mode_window
import Theorems.Thm_mme_released_joint_interior_owner_fine_partition
import Theorems.Thm_mme_released_joint_interior_owner_mass
import Theorems.Thm_mme_profiled_CW_regroup_product_restrict

open scoped BigOperators
open MME MME.TensorObj MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed
universe u

/-- The full graded joint source restricts the released interior owner-window
product in common mode order. All target addresses remain available; an address
is chosen only to establish a single mode's window condition. -/
theorem solution
    {K : Type u} [Field K] (k : ℕ) (hk : 0 < k)
    (eps : ℝ) :
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
    let Q : ∀ r : Fin 6, ProfiledCW.Predicate (blocks r k * 4) :=
      fun r i x => gradedSource r k eps ((roleEquiv r).symm i) x
    Restrict (kronFin 6 (fun r => ProfiledCW.tensor K (Q r)))
      (kronFin 270 (fun j => ProfiledCW.tensor K (P j))) := by
  classical
  intro P Q
  have hi (j : Fin 270) (hw : 0 < weight j) :
      (ReleasedInterior.seed (component j).1 (component j).2).boundary = [] := by
    by_contra h
    have hz : weight j = 0 := by simp only [weight, if_neg h]
    omega
  let defaultE (j : Fin 270) :
      Fin ((k * weight j * denominator ^ 4) * 2) ≃ Position (fun r => size r k j) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_fin, Fintype.card_sigma, Fintype.card_prod,
        ← Finset.sum_mul, mme_released_joint_interior_owner_mass])
  let e (j : Fin 270) :
      Fin ((k * weight j * denominator ^ 4) * 2) ≃ Position (fun r => size r k j) :=
    if hw : 0 < weight j then
      Classical.choose (mme_released_joint_interior_common_mode_window k hk j hw (hi j hw))
    else defaultE j
  let length (j : Fin 270) :
      ((k * weight j * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
        (k * weight j * denominator ^ 4) * 4 := by omega
  obtain ⟨E, hE⟩ := mme_released_joint_interior_owner_fine_partition k
    (fun j => (k * weight j * denominator ^ 4) * 2)
    (fun j => (k * weight j * denominator ^ 4) * 4) e length
  apply mme_profiled_CW_regroup_product_restrict
    (fun j => (k * weight j * denominator ^ 4) * 4)
    (fun r => blocks r k * 4) E P Q
  intro i x hx j hw
  have he := Classical.choose_spec
    (mme_released_joint_interior_common_mode_window k hk j hw (hi j hw))
  have ha : ∀ r : Fin 6, ∃ a : Address 4 270 (parent r) (size r k),
      Graded (parent_total r) ((roleEquiv r).symm i) a
        (ProfiledCW.split (positions r k) (positions_length r k) (x r)) := by
    intro r
    obtain ⟨a, _, hg⟩ := (hx r).2
    exact ⟨a, hg⟩
  choose a hg using ha
  have hwindow := he i a x eps hg (fun r => (hx r).1)
  have heq : e j = Classical.choose
      (mme_released_joint_interior_common_mode_window k hk j hw (hi j hw)) := by
    simp only [e, dif_pos hw]
  have hz : (fun q => x (E ⟨j,q⟩).1 (E ⟨j,q⟩).2) =
      (fun q => x (ownerFineEmbedding k j (e j) (length j) q).1
        (ownerFineEmbedding k j (e j) (length j) q).2) := by
    funext q
    rw [hE j q]
  rw [hz, heq]
  exact hwindow


#print axioms solution
