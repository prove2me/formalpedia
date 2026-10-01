-- Prove2me | solution 1 for mme_released_positive_region4_profile_reindex
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:34:04.927297+00:00
-- url     : https://prove2.me/submissions/b9bead3a-56c4-4a61-87fb-cbc63aa98867

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_profiles
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MME MME.RecursiveYZ

namespace PositiveRegionBridge4

private def componentIndex : Fin 88 → Fin 270 :=
  ![10,13,14,15,20,21,22,26,28,31,32,36,37,40,60,59,57,56,55,66,65,64,63,72,70,78,77,82,81,85,100,121,126,130,116,127,110,123,103,111,104,112,105,150,157,168,172,175,156,162,171,155,166,147,154,146,145,220,216,205,198,190,212,206,199,191,207,192,208,201,202,194,195,265,262,253,247,240,257,252,246,239,251,238,250,244,243,235]

private def inverseIndex : Fin 270 → Fin 88 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,0,0,0,0,4,5,6,0,0,0,7,0,8,0,0,9,10,0,0,0,11,12,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,17,16,0,15,14,0,0,22,21,20,19,0,0,0,24,0,23,0,0,0,0,26,25,0,0,28,27,0,0,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,30,0,0,38,40,42,0,0,0,0,36,39,41,0,0,0,34,0,0,0,0,31,0,37,0,0,32,35,0,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,56,55,53,0,0,43,0,0,0,54,51,48,44,0,0,0,0,49,0,0,0,52,0,45,0,0,50,46,0,0,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,61,65,67,0,71,72,0,0,60,64,0,69,70,0,0,59,63,66,68,0,0,0,62,0,0,0,58,0,0,0,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,87,0,0,83,81,77,0,0,86,85,0,80,76,0,0,84,82,79,75,0,0,0,78,0,0,0,0,74,0,0,73,0,0,0,0]

private theorem component_positive : ∀ r : Fin 88,
    0 < ReleasedJointInterior.size 4 1 (componentIndex r) := by
  decide +kernel

private theorem left_inverse : ∀ r : Fin 88,
    inverseIndex (componentIndex r) = r := by
  decide +kernel

private theorem right_inverse : ∀ j : Fin 270,
    0 < ReleasedJointInterior.size 4 1 j →
      componentIndex (inverseIndex j) = j := by
  decide +kernel

private def indexEquiv :
    Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 4 1 j} where
  toFun r := ⟨componentIndex r, component_positive r⟩
  invFun j := inverseIndex j.val
  left_inv := left_inverse
  right_inv j := Subtype.ext (right_inverse j.val j.property)

private theorem parent_match : ∀ r : Fin 88,
    RecStage.parent3 4 r = ReleasedJointInterior.parent 4 (componentIndex r) := by
  decide +kernel

private theorem size_match : ∀ r : Fin 88,
    ReleasedJointInterior.size 4 1 (componentIndex r) = RecStage.n3 4 r := by
  decide +kernel

private def mapSplit (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 4 r)) :
    RecursiveThinSplit.Split 4 (ReleasedJointInterior.parent 4 (componentIndex r)) :=
  ⟨c.val, by rw [← parent_match r]; exact c.property⟩

private theorem split_match : ∀ (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 4 r)),
    ReleasedJointInterior.splitCount 4 1 (componentIndex r) (mapSplit r c) =
      RecStage.m3 4 r c := by
  intro r
  fin_cases r <;> decide +kernel

private theorem profile_match : ∀ (r : Fin 88) (i : Fin 3)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 4 r)) (w : CompleteSplit.CompleteWord 2),
    ReleasedJointInterior.integerProfile 4 1 i ⟨componentIndex r, mapSplit r c⟩ w =
      RecStage.mu3 4 i ⟨r, c⟩ w := by
  intro r
  fin_cases r <;> decide +kernel

private theorem split_cast_val {p q : Fin 3 → ℕ} (h : p = q)
    (c : RecursiveThinSplit.Split 4 p) :
    (Eq.mp (congrArg (RecursiveThinSplit.Split 4) h) c).val = c.val := by
  cases h
  rfl

private theorem mapSplit_eq_cast (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 4 r)) :
    mapSplit r c =
      Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c := by
  apply Subtype.ext
  exact (split_cast_val (parent_match r) c).symm

end PositiveRegionBridge4

open PositiveRegionBridge4

/-- The compact recursive region is exactly the positive part of the common
owner and parent profile, with identical integer counts at every scale. -/
theorem solution :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 4 1 j})
      (hparent : ∀ r, RecStage.parent3 4 r = ReleasedJointInterior.parent 4 (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size 4 k (e r).val = k * RecStage.n3 4 r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 4 r)),
          ReleasedJointInterior.splitCount 4 k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c) =
              k * RecStage.m3 4 r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 4 r))
          (w : CompleteSplit.CompleteWord 2),
          ReleasedJointInterior.integerProfile 4 k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c⟩ w =
              k * RecStage.mu3 4 i ⟨r, c⟩ w) := by
  refine ⟨indexEquiv, parent_match, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa only [ReleasedJointInterior.size, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (size_match r)
  · intro r c
    change ReleasedJointInterior.splitCount 4 k (componentIndex r)
      (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c) = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.splitCount, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (split_match r c)
  · intro i r c w
    change ReleasedJointInterior.integerProfile 4 k i
      ⟨componentIndex r, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c⟩ w = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.integerProfile, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (profile_match r i c w)

#print axioms solution
