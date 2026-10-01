-- Prove2me | solution 1 for mme_released_positive_region2_profile_reindex
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:13:54.953482+00:00
-- url     : https://prove2.me/submissions/5d0075e5-87f1-4759-bce9-1b01a0d266f4

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_profiles
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MME MME.RecursiveYZ

namespace PositiveRegionBridge2

private def componentIndex : Fin 88 → Fin 270 :=
  ![10,11,12,14,15,18,19,20,21,25,27,32,33,36,37,40,60,59,58,55,67,66,65,73,71,77,76,82,81,85,100,108,115,126,130,101,109,116,122,102,117,111,118,104,112,105,150,157,163,172,175,149,156,162,167,148,161,154,160,153,145,220,216,211,190,217,206,213,200,201,193,202,194,195,265,262,258,247,240,261,252,246,256,245,244,237,236,235]

private def inverseIndex : Fin 270 → Fin 88 :=
  ![0,0,0,0,0,0,0,0,0,0,0,1,2,0,3,4,0,0,5,6,7,8,0,0,0,9,0,10,0,0,0,0,11,12,0,0,13,14,0,0,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19,0,0,18,17,16,0,0,0,0,22,21,20,0,0,0,24,0,23,0,0,26,25,0,0,0,28,27,0,0,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,30,35,39,0,43,45,0,0,31,36,0,41,44,0,0,32,37,40,42,0,0,0,38,0,0,0,33,0,0,0,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,60,0,0,55,51,46,0,0,59,57,0,52,47,0,0,58,56,53,48,0,0,0,54,0,0,0,0,49,0,0,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,70,72,73,0,0,0,0,68,69,71,0,0,0,66,0,0,0,0,63,0,67,0,0,62,65,0,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,87,86,85,0,0,78,0,0,0,84,83,81,77,0,0,0,0,80,0,0,0,82,0,76,0,0,79,75,0,0,74,0,0,0,0]

private theorem component_positive : ∀ r : Fin 88,
    0 < ReleasedJointInterior.size 2 1 (componentIndex r) := by
  decide +kernel

private theorem left_inverse : ∀ r : Fin 88,
    inverseIndex (componentIndex r) = r := by
  decide +kernel

private theorem right_inverse : ∀ j : Fin 270,
    0 < ReleasedJointInterior.size 2 1 j →
      componentIndex (inverseIndex j) = j := by
  decide +kernel

private def indexEquiv :
    Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 2 1 j} where
  toFun r := ⟨componentIndex r, component_positive r⟩
  invFun j := inverseIndex j.val
  left_inv := left_inverse
  right_inv j := Subtype.ext (right_inverse j.val j.property)

private theorem parent_match : ∀ r : Fin 88,
    RecStage.parent3 2 r = ReleasedJointInterior.parent 2 (componentIndex r) := by
  decide +kernel

private theorem size_match : ∀ r : Fin 88,
    ReleasedJointInterior.size 2 1 (componentIndex r) = RecStage.n3 2 r := by
  decide +kernel

private def mapSplit (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 2 r)) :
    RecursiveThinSplit.Split 4 (ReleasedJointInterior.parent 2 (componentIndex r)) :=
  ⟨c.val, by rw [← parent_match r]; exact c.property⟩

private theorem split_match : ∀ (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 2 r)),
    ReleasedJointInterior.splitCount 2 1 (componentIndex r) (mapSplit r c) =
      RecStage.m3 2 r c := by
  intro r
  fin_cases r <;> decide +kernel

private theorem profile_match : ∀ (r : Fin 88) (i : Fin 3)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 2 r)) (w : CompleteSplit.CompleteWord 2),
    ReleasedJointInterior.integerProfile 2 1 i ⟨componentIndex r, mapSplit r c⟩ w =
      RecStage.mu3 2 i ⟨r, c⟩ w := by
  intro r
  fin_cases r <;> decide +kernel

private theorem split_cast_val {p q : Fin 3 → ℕ} (h : p = q)
    (c : RecursiveThinSplit.Split 4 p) :
    (Eq.mp (congrArg (RecursiveThinSplit.Split 4) h) c).val = c.val := by
  cases h
  rfl

private theorem mapSplit_eq_cast (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 2 r)) :
    mapSplit r c =
      Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c := by
  apply Subtype.ext
  exact (split_cast_val (parent_match r) c).symm

end PositiveRegionBridge2

open PositiveRegionBridge2

/-- The compact recursive region is exactly the positive part of the common
owner and parent profile, with identical integer counts at every scale. -/
theorem solution :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 2 1 j})
      (hparent : ∀ r, RecStage.parent3 2 r = ReleasedJointInterior.parent 2 (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size 2 k (e r).val = k * RecStage.n3 2 r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 2 r)),
          ReleasedJointInterior.splitCount 2 k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c) =
              k * RecStage.m3 2 r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 2 r))
          (w : CompleteSplit.CompleteWord 2),
          ReleasedJointInterior.integerProfile 2 k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c⟩ w =
              k * RecStage.mu3 2 i ⟨r, c⟩ w) := by
  refine ⟨indexEquiv, parent_match, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa only [ReleasedJointInterior.size, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (size_match r)
  · intro r c
    change ReleasedJointInterior.splitCount 2 k (componentIndex r)
      (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c) = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.splitCount, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (split_match r c)
  · intro i r c w
    change ReleasedJointInterior.integerProfile 2 k i
      ⟨componentIndex r, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c⟩ w = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.integerProfile, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (profile_match r i c w)

#print axioms solution
