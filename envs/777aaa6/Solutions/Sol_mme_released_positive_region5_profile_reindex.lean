-- Prove2me | solution 1 for mme_released_positive_region5_profile_reindex
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:38:28.609793+00:00
-- url     : https://prove2.me/submissions/ec263fae-622f-43d2-896a-08e7b86c5add

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_profiles
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MME MME.RecursiveYZ

namespace PositiveRegionBridge5

private def componentIndex : Fin 88 → Fin 270 :=
  ![10,13,14,15,20,21,22,26,31,33,36,37,40,60,57,56,55,67,66,65,64,72,78,76,82,81,85,100,121,126,130,116,122,127,110,103,111,118,104,112,105,150,168,172,175,149,156,162,167,171,155,147,154,160,146,153,145,220,205,198,190,217,212,206,199,207,208,201,193,202,194,195,265,253,247,240,261,257,252,246,239,251,250,244,237,243,236,235]

private def inverseIndex : Fin 270 → Fin 88 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,0,0,0,0,4,5,6,0,0,0,7,0,0,0,0,8,0,9,0,0,10,11,0,0,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,15,14,0,0,13,0,0,0,20,19,18,17,0,0,0,0,21,0,0,0,23,0,22,0,0,25,24,0,0,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,27,0,0,35,38,40,0,0,0,0,34,36,39,0,0,0,31,0,37,0,0,28,32,0,0,0,29,33,0,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,56,54,51,0,45,41,0,0,55,52,50,46,0,0,0,53,0,47,0,0,0,0,48,42,0,0,49,43,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,60,0,0,68,70,71,0,0,59,64,0,67,69,0,0,58,63,65,66,0,0,0,62,0,0,0,0,61,0,0,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,87,86,84,0,80,75,0,0,85,83,0,79,74,0,0,82,81,78,73,0,0,0,77,0,0,0,76,0,0,0,72,0,0,0,0]

private theorem component_positive : ∀ r : Fin 88,
    0 < ReleasedJointInterior.size 5 1 (componentIndex r) := by
  decide +kernel

private theorem left_inverse : ∀ r : Fin 88,
    inverseIndex (componentIndex r) = r := by
  decide +kernel

private theorem right_inverse : ∀ j : Fin 270,
    0 < ReleasedJointInterior.size 5 1 j →
      componentIndex (inverseIndex j) = j := by
  decide +kernel

private def indexEquiv :
    Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 5 1 j} where
  toFun r := ⟨componentIndex r, component_positive r⟩
  invFun j := inverseIndex j.val
  left_inv := left_inverse
  right_inv j := Subtype.ext (right_inverse j.val j.property)

private theorem parent_match : ∀ r : Fin 88,
    RecStage.parent3 5 r = ReleasedJointInterior.parent 5 (componentIndex r) := by
  decide +kernel

private theorem size_match : ∀ r : Fin 88,
    ReleasedJointInterior.size 5 1 (componentIndex r) = RecStage.n3 5 r := by
  decide +kernel

private def mapSplit (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 5 r)) :
    RecursiveThinSplit.Split 4 (ReleasedJointInterior.parent 5 (componentIndex r)) :=
  ⟨c.val, by rw [← parent_match r]; exact c.property⟩

private theorem split_match : ∀ (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 5 r)),
    ReleasedJointInterior.splitCount 5 1 (componentIndex r) (mapSplit r c) =
      RecStage.m3 5 r c := by
  intro r
  fin_cases r <;> decide +kernel

private theorem profile_match : ∀ (r : Fin 88) (i : Fin 3)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 5 r)) (w : CompleteSplit.CompleteWord 2),
    ReleasedJointInterior.integerProfile 5 1 i ⟨componentIndex r, mapSplit r c⟩ w =
      RecStage.mu3 5 i ⟨r, c⟩ w := by
  intro r
  fin_cases r <;> decide +kernel

private theorem split_cast_val {p q : Fin 3 → ℕ} (h : p = q)
    (c : RecursiveThinSplit.Split 4 p) :
    (Eq.mp (congrArg (RecursiveThinSplit.Split 4) h) c).val = c.val := by
  cases h
  rfl

private theorem mapSplit_eq_cast (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 5 r)) :
    mapSplit r c =
      Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c := by
  apply Subtype.ext
  exact (split_cast_val (parent_match r) c).symm

end PositiveRegionBridge5

open PositiveRegionBridge5

/-- The compact recursive region is exactly the positive part of the common
owner and parent profile, with identical integer counts at every scale. -/
theorem solution :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 5 1 j})
      (hparent : ∀ r, RecStage.parent3 5 r = ReleasedJointInterior.parent 5 (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size 5 k (e r).val = k * RecStage.n3 5 r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 5 r)),
          ReleasedJointInterior.splitCount 5 k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c) =
              k * RecStage.m3 5 r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 5 r))
          (w : CompleteSplit.CompleteWord 2),
          ReleasedJointInterior.integerProfile 5 k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c⟩ w =
              k * RecStage.mu3 5 i ⟨r, c⟩ w) := by
  refine ⟨indexEquiv, parent_match, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa only [ReleasedJointInterior.size, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (size_match r)
  · intro r c
    change ReleasedJointInterior.splitCount 5 k (componentIndex r)
      (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c) = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.splitCount, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (split_match r c)
  · intro i r c w
    change ReleasedJointInterior.integerProfile 5 k i
      ⟨componentIndex r, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c⟩ w = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.integerProfile, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (profile_match r i c w)

#print axioms solution
