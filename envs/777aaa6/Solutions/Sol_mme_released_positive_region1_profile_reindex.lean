-- Prove2me | solution 1 for mme_released_positive_region1_profile_reindex
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:08:36.713648+00:00
-- url     : https://prove2.me/submissions/e4e6c3ed-9125-452c-bf09-36f9f5d68cbf

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_profiles
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MME MME.RecursiveYZ

namespace PositiveRegionBridge1

private def componentIndex : Fin 88 → Fin 270 :=
  ![10,13,14,15,18,19,21,22,25,26,27,28,32,37,40,60,59,57,56,55,67,66,64,63,73,72,71,70,77,81,85,100,121,126,130,101,109,127,102,110,117,123,111,112,105,150,157,168,172,175,149,156,171,148,155,161,166,145,220,216,205,198,190,217,212,199,191,213,207,200,192,201,194,195,265,262,253,247,240,261,257,246,239,256,251,245,238,235]

private def inverseIndex : Fin 270 → Fin 88 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,0,0,4,5,0,6,7,0,0,8,9,10,11,0,0,0,12,0,0,0,0,13,0,0,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19,18,17,0,16,15,0,0,23,22,0,21,20,0,0,27,26,25,24,0,0,0,28,0,0,0,29,0,0,0,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,35,38,0,0,44,0,0,0,36,39,42,43,0,0,0,0,40,0,0,0,32,0,41,0,0,33,37,0,0,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,57,0,0,53,50,45,0,0,0,0,54,51,46,0,0,0,55,0,0,0,0,56,0,47,0,0,52,48,0,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,62,66,70,0,72,73,0,0,61,65,69,71,0,0,0,60,0,68,0,0,0,0,64,67,0,0,59,63,0,0,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,87,0,0,86,82,78,0,0,0,0,85,81,77,0,0,0,84,0,76,0,0,83,80,0,0,0,79,75,0,0,74,0,0,0,0]

private theorem component_positive : ∀ r : Fin 88,
    0 < ReleasedJointInterior.size 1 1 (componentIndex r) := by
  decide +kernel

private theorem left_inverse : ∀ r : Fin 88,
    inverseIndex (componentIndex r) = r := by
  decide +kernel

private theorem right_inverse : ∀ j : Fin 270,
    0 < ReleasedJointInterior.size 1 1 j →
      componentIndex (inverseIndex j) = j := by
  decide +kernel

private def indexEquiv :
    Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 1 1 j} where
  toFun r := ⟨componentIndex r, component_positive r⟩
  invFun j := inverseIndex j.val
  left_inv := left_inverse
  right_inv j := Subtype.ext (right_inverse j.val j.property)

private theorem parent_match : ∀ r : Fin 88,
    RecStage.parent3 1 r = ReleasedJointInterior.parent 1 (componentIndex r) := by
  decide +kernel

private theorem size_match : ∀ r : Fin 88,
    ReleasedJointInterior.size 1 1 (componentIndex r) = RecStage.n3 1 r := by
  decide +kernel

private def mapSplit (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 1 r)) :
    RecursiveThinSplit.Split 4 (ReleasedJointInterior.parent 1 (componentIndex r)) :=
  ⟨c.val, by rw [← parent_match r]; exact c.property⟩

private theorem split_match : ∀ (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 1 r)),
    ReleasedJointInterior.splitCount 1 1 (componentIndex r) (mapSplit r c) =
      RecStage.m3 1 r c := by
  intro r
  fin_cases r <;> decide +kernel

private theorem profile_match : ∀ (r : Fin 88) (i : Fin 3)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 1 r)) (w : CompleteSplit.CompleteWord 2),
    ReleasedJointInterior.integerProfile 1 1 i ⟨componentIndex r, mapSplit r c⟩ w =
      RecStage.mu3 1 i ⟨r, c⟩ w := by
  intro r
  fin_cases r <;> decide +kernel

private theorem split_cast_val {p q : Fin 3 → ℕ} (h : p = q)
    (c : RecursiveThinSplit.Split 4 p) :
    (Eq.mp (congrArg (RecursiveThinSplit.Split 4) h) c).val = c.val := by
  cases h
  rfl

private theorem mapSplit_eq_cast (r : Fin 88)
    (c : RecursiveThinSplit.Split 4 (RecStage.parent3 1 r)) :
    mapSplit r c =
      Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c := by
  apply Subtype.ext
  exact (split_cast_val (parent_match r) c).symm

end PositiveRegionBridge1

open PositiveRegionBridge1

/-- The compact recursive region is exactly the positive part of the common
owner and parent profile, with identical integer counts at every scale. -/
theorem solution :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size 1 1 j})
      (hparent : ∀ r, RecStage.parent3 1 r = ReleasedJointInterior.parent 1 (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size 1 k (e r).val = k * RecStage.n3 1 r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 1 r)),
          ReleasedJointInterior.splitCount 1 k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c) =
              k * RecStage.m3 1 r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 1 r))
          (w : CompleteSplit.CompleteWord 2),
          ReleasedJointInterior.integerProfile 1 k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c⟩ w =
              k * RecStage.mu3 1 i ⟨r, c⟩ w) := by
  refine ⟨indexEquiv, parent_match, ?_⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · intro r
    simpa only [ReleasedJointInterior.size, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (size_match r)
  · intro r c
    change ReleasedJointInterior.splitCount 1 k (componentIndex r)
      (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c) = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.splitCount, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (split_match r c)
  · intro i r c w
    change ReleasedJointInterior.integerProfile 1 k i
      ⟨componentIndex r, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (parent_match r)) c⟩ w = _
    rw [← mapSplit_eq_cast]
    simpa only [ReleasedJointInterior.integerProfile, Nat.one_mul, Nat.mul_assoc] using
      congrArg (fun n => k * n) (profile_match r i c w)

#print axioms solution
