-- Prove2me | solution 1 for mme_released_joint_interior_common_mode_window
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:33.710558+00:00
-- url     : https://prove2.me/submissions/74d28fc7-5277-4bb5-921f-2af86b807540

import Theorems.Thm_mme_released_joint_interior_selected_owner_window

open scoped BigOperators
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed

/-- A common source mode induces the same mode in a joint region for every
owner. Returning the outer owners to source order therefore recovers their
released windows without choosing different modes within a joint region. -/
theorem solution
    (k : ℕ) (hk : 0 < k) (j : Fin 270) (hw : 0 < weight j)
    (hi : (ReleasedInterior.seed (component j).1 (component j).2).boundary = []) :
    ∃ e : Fin ((k * weight j * denominator ^ 4) * 2) ≃
        Position (fun r => size r k j),
      ∀ (i : Fin 3) (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
        (x : ∀ r : Fin 6, ProfiledCW.FineWord (blocks r k * 4)) (eps : ℝ),
        (∀ r : Fin 6,
          Graded (parent_total r) ((roleEquiv r).symm i) (a r)
            (ProfiledCW.split (positions r k) (positions_length r k)
              (x r))) →
        (∀ r : Fin 6,
          source r k eps ((roleEquiv r).symm i)
            (x r)) →
        let length : ((k * weight j * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * weight j * denominator ^ 4) * 4 := by omega
        let z := fun q =>
          let t := ownerFineEmbedding k j e length q
          x t.1 t.2
        (∀ p : Fin (k * weight j * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p q).val) =
            ReleasedInterior.parent (component j).2 0 ((roleEquiv (component j).1).symm i)) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * weight j * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p = w} : ℝ) /
              (k * weight j * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows (component j).1 (component j).2).map
              (fun p => if ReleasedGlobal.atom p.1 ((roleEquiv (component j).1).symm i) = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps  := by
  obtain ⟨e, he⟩ := mme_released_joint_interior_selected_owner_window k hk j hw hi
  refine ⟨e, ?_⟩
  intro i a x eps hg ht
  have hmode (r : Fin 6) :
      (orientation (component j).1 r).symm ((roleEquiv (component j).1).symm i) =
        (roleEquiv r).symm i := by
    simp only [orientation, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  have hg' : ∀ r : Fin 6,
      Graded (parent_total r)
        ((orientation (component j).1 r).symm ((roleEquiv (component j).1).symm i))
        (a r) (ProfiledCW.split (positions r k) (positions_length r k) (x r)) := by
    intro r
    rw [hmode r]
    exact hg r
  have ht' : ∀ r : Fin 6,
      source r k eps
        ((orientation (component j).1 r).symm ((roleEquiv (component j).1).symm i))
        (x r) := by
    intro r
    rw [hmode r]
    exact ht r
  exact he ((roleEquiv (component j).1).symm i) a (fun r _ => x r) eps hg' ht'


#print axioms solution
