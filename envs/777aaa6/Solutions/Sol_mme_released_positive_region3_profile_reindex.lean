-- Prove2me | solution 1 for mme_released_positive_region3_profile_reindex
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:26:09.486708+00:00
-- url     : https://prove2.me/submissions/c4eb0dc2-452a-47da-9344-80c3020894ff

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_profiles
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MME MME.RecursiveYZ

namespace PositiveRegionBridge3

private def componentIndex : Fin 88 → Fin 270 :=
  ![10,11,12,15,19,20,21,22,27,31,33,36,37,40,60,59,58,55,67,66,65,71,78,76,82,81,85,100,108,115,130,109,116,122,127,117,103,111,118,104,112,105,150,157,163,175,149,156,162,167,171,161,147,154,160,146,153,145,220,216,211,190,217,212,206,200,208,201,193,202,194,195,265,262,258,240,261,257,252,246,239,245,250,244,237,243,236,235]

private def inverseIndex : Fin 270 → Fin 88 :=
  ![0,0,0,0,0,0,0,0,0,0,0,1,2,0,0,3,0,0,0,4,5,6,7,0,0,0,0,8,0,0,0,9,0,10,0,0,11,12,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,0,0,16,15,14,0,0,0,0,20,19,18,0,0,0,21,0,0,0,0,23,0,22,0,0,25,24,0,0,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,27,0,0,36,39,41,0,0,28,31,0,37,40,0,0,29,32,35,38,0,0,0,33,0,0,0,0,34,0,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,57,55,52,0,46,42,0,0,56,53,0,47,43,0,0,54,51,48,44,0,0,0,49,0,0,0,50,0,0,0,45,0,0,0,0,0,0,0,0,0,0,0,0,0,0,61,0,0,68,70,71,0,0,0,0,65,67,69,0,0,0,64,0,66,0,0,60,63,0,0,0,59,62,0,0,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,87,86,84,0,80,75,0,0,85,83,81,79,0,0,0,82,0,78,0,0,0,0,77,74,0,0,76,73,0,0,72,0,0,0,0]

private theorem component_positive : ∀ r : Fin 88,
    0 < ReleasedJointInterior.size 3 1 (componentIndex r) := by
  decide +kernel

private theorem left_inverse : ∀ r : Fin 88,
    inverseIndex (componentIndex r) = r := by
  decide +kernel

private theorem right_inverse : ∀ j : Fin 270,
    0 < ReleasedJointInterior.size 3 1 j →
      componentIndex (inverseIndex j) = j := by
  decide +kernel

private def indexEquiv :
    Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 3 1 j} where
  toFun r := ⟨componentIndex r, component_positive r⟩
  invFun j := inverseIndex j.val
  left_inv := left_inverse
  right_inv j := Subtype.ext (right_inverse j.val j.property)

private theorem parent_match : ∀ r : Fin 88,
    RecStage.parent3 3 r = ReleasedJointInterior.parent 3 (componentIndex r) := by
  decide +kernel

private theorem size_match : ∀ r : Fin 88,
    ReleasedJointInterior.size 3 1 (componentIndex r) = RecStage.n3 3 r := by
  decide +kernel

private def mapSplit (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 3 r)) :
    RecursiveThinSplit.Split 4 (ReleasedJointInterior.parent 3 (componentIndex r)) :=
  ⟨c.val, by rw [← parent_match r]; exact c.property⟩

private theorem split_match : ∀ (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 3 r)),
    ReleasedJointInterior.splitCount 3 1 (componentIndex r) (mapSplit r c) =
      RecStage.m3 3 r c := by
  intro r
  fin_cases r <;> decide +kernel

private theorem profile_match : ∀ (r : Fin 88) (i : Fin 3)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 3 r)) (w : CompleteSplit.CompleteWord 2),
    ReleasedJointInterior.integerProfile 3 1 i ⟨componentIndex r, mapSplit r c⟩ w =
      RecStage.mu3 3 i ⟨r, c⟩ w := by
  intro r
  fin_cases r <;> decide +kernel

private theorem split_cast_val {p q : Fin 3 → ℕ} (h : p = q)
    (c : RecursiveThinSplit.Split 4 p) :
    (Eq.mp (congrArg (RecursiveThinSplit.Split 4) h) c).val = c.val := by
  cases h
  rfl

private theorem mapSplit_eq_cast (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 3 r)) :
    mapSplit r c =
      Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c := by
  apply Subtype.ext
  exact (split_cast_val (parent_match r) c).symm

end PositiveRegionBridge3

open PositiveRegionBridge3

/-- The compact recursive region is exactly the positive part of the common
owner and parent profile, with identical integer counts at every scale. -/
theorem solution :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 3 1 j})
      (hparent : ∀ r, RecStage.parent3 3 r = ReleasedJointInterior.parent 3 (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size 3 k (e r).val = k * RecStage.n3 3 r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 3 r)),
          ReleasedJointInterior.splitCount 3 k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c) =
              k * RecStage.m3 3 r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 3 r))
          (w : CompleteSplit.CompleteWord 2),
          ReleasedJointInterior.integerProfile 3 k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c⟩ w =
              k * RecStage.mu3 3 i ⟨r, c⟩ w) := by
  refine ⟨indexEquiv, parent_match, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa only [ReleasedJointInterior.size, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (size_match r)
  · intro r c
    change ReleasedJointInterior.splitCount 3 k (componentIndex r)
      (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c) = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.splitCount, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (split_match r c)
  · intro i r c w
    change ReleasedJointInterior.integerProfile 3 k i
      ⟨componentIndex r, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c⟩ w = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.integerProfile, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (profile_match r i c w)

#print axioms solution
