-- Prove2me | solution 1 for mme_released_joint_interior_zero_owner_output
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:59:26.501293+00:00
-- url     : https://prove2.me/submissions/949d1baf-500d-461f-83a4-9c29cd4de4fd

import Definitions.Def_mme_released_joint_interior_frame
import Theorems.Thm_mme_profiled_CW_empty_six_extraction

open MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed
universe u

/-- A zero-weight owner occupies no coordinates and its exact output
contributes a scalar matrix tensor, with no loss in the product weight. -/
theorem solution
    {K : Type u} [Field K] (k : ℕ) (j : Fin 270) (hw : weight j = 0)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    {L N : ℕ} (e : Fin L ≃ Position (fun r => size r k j))
    (length : L * 2 ^ (2 - 1) = N) (sigma : Equiv.Perm (Fin 3)) :
    Restrict (MMObj K 1 1 1)
      (sixSymmetrization (ProfiledCW.tensor K (fun i x =>
        Graded (ReleasedInterior.parent_total (component j).2) (sigma.symm i)
          (fun r t => (splitEquiv r j).symm (a r j t))
          (ProfiledCW.split e length x) ∧
        Useful (fullCell (ReleasedInterior.parent_total (component j).2)
          (fun r t => (splitEquiv r j).symm (a r j t)))
          (fun c w => k * weight j * ReleasedInterior.integerProfile
            (component j).1 (component j).2 (sigma.symm i) c w)
          (ProfiledCW.split e length x)))) := by
  classical
  letI : IsEmpty (Position (fun r => size r k j)) := ⟨by
    rintro ⟨r,t,h⟩
    have ht := t.isLt
    simp only [size, hw, mul_zero, zero_mul] at ht
    exact Nat.not_lt_zero _ ht⟩
  have hL : L = 0 := by
    have hcard := Fintype.card_congr e
    simpa only [Fintype.card_fin, Fintype.card_of_isEmpty] using hcard
  have hN : N = 0 := by omega
  apply mme_profiled_CW_empty_six_extraction hN
  intro i x
  constructor
  · intro p
    exact isEmptyElim p
  · simp [Useful, count, hw]


#print axioms solution
