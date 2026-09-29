-- Prove2me | Definitions.Def_mme_released_global_profile_data
-- name    : mme_released_global_profile_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T11:18:44.802985+00:00
-- url     : https://prove2.me/theorems/c8a3c5b8-f6fb-4454-a790-c3d6d8fe2da4
-- title:
--   Exact rational global profile from the concrete supported table
-- statement:
--   The 45 coarse shapes and their equivalence to the split subtype, supported-atom decoding, integer joint and marginal counts, and the central normalized profile with common denominator 10^60.
-- source:
--   Concrete released-profile realization for the unpaired global stage of More Asymmetry Theorem 5.3.

import Definitions.Def_mme_released_global_joint_counts
import Definitions.Def_mme_global_CW_real_entropy_profiles
import Definitions.Def_mme_global_CW_histogram_frame
import Mathlib
open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace MME.ReleasedGlobal

abbrev Shape := RecursiveThinSplit.Split 8 (fun _ ↦ 8)
abbrev Word := CompleteWord 3
abbrev JointWord := Fin 3 → Word

def shapeVector : Fin 45 → Fin 3 → Fin 9 :=
  ![![0,0,8],
    ![0,1,7],
    ![0,2,6],
    ![0,3,5],
    ![0,4,4],
    ![0,5,3],
    ![0,6,2],
    ![0,7,1],
    ![0,8,0],
    ![1,0,7],
    ![1,1,6],
    ![1,2,5],
    ![1,3,4],
    ![1,4,3],
    ![1,5,2],
    ![1,6,1],
    ![1,7,0],
    ![2,0,6],
    ![2,1,5],
    ![2,2,4],
    ![2,3,3],
    ![2,4,2],
    ![2,5,1],
    ![2,6,0],
    ![3,0,5],
    ![3,1,4],
    ![3,2,3],
    ![3,3,2],
    ![3,4,1],
    ![3,5,0],
    ![4,0,4],
    ![4,1,3],
    ![4,2,2],
    ![4,3,1],
    ![4,4,0],
    ![5,0,3],
    ![5,1,2],
    ![5,2,1],
    ![5,3,0],
    ![6,0,2],
    ![6,1,1],
    ![6,2,0],
    ![7,0,1],
    ![7,1,0],
    ![8,0,0]]

def shape (s : Fin 45) : Shape :=
  ⟨shapeVector s, (by decide +kernel : ∀ s : Fin 45,
    ((shapeVector s 0).val + (shapeVector s 1).val + (shapeVector s 2).val = 8 ∧
    ∀ i, (shapeVector s i).val ≤ 8)) s⟩

def shapeIndex (c : Shape) : ℕ :=
  9*(c.val 0).val - (c.val 0).val*((c.val 0).val-1)/2 + (c.val 1).val

noncomputable def shapeEquiv : Fin 45 ≃ Shape :=
  Equiv.ofBijective shape (by
    have hleft : ∀ s : Fin 45, shapeIndex (shape s) = s.val := by decide +kernel
    have hinj : Function.Injective shape := by
      intro a b h
      apply Fin.ext
      simpa only [hleft] using congrArg shapeIndex h
    apply (Fintype.bijective_iff_injective_and_card shape).mpr
    refine ⟨hinj,?_⟩
    decide +kernel)

def alpha (owner : Fin 6) (s : Fin 45) : ℕ :=
  (MoreAsymmetryExactSeed.globalAlpha.getD owner.val []).getD (sourceIndex owner s).val 0

def elementary : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,0,2],![0,1,1],![0,2,0],![1,0,1],![1,1,0],![2,0,0]]

def atom (a : Fin 1296) : JointWord :=
  fun i r ↦ elementary ⟨a.val / 6^r.val % 6, Nat.mod_lt _ (by decide)⟩ i

def rowCounts (owner : Fin 6) (s : Fin 45) (v : JointWord) : ℕ :=
  ((jointRows owner s).map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum

noncomputable def jointCounts (owner : Fin 6) (c : Shape) (v : JointWord) : ℕ :=
  alpha owner (shapeEquiv.symm c) * rowCounts owner (shapeEquiv.symm c) v

noncomputable def coarseCounts (owner : Fin 6) (c : Shape) : ℕ :=
  alpha owner (shapeEquiv.symm c) * MoreAsymmetryExactSeed.denominator^4

noncomputable def wordCounts (owner : Fin 6) (i : Fin 3) (c : Shape) (w : Word) : ℕ :=
  ∑ v : JointWord, if v i = w then jointCounts owner c v else 0

noncomputable def profile (owner : Fin 6) : GlobalCW.EntropyProfile 8 1 (fun _ _ ↦ 8) Word :=
  (fun _ c ↦ (coarseCounts owner c : ℝ) / (MoreAsymmetryExactSeed.denominator : ℝ)^5,
   fun i c w ↦ (wordCounts owner i c.2 w : ℝ) / (MoreAsymmetryExactSeed.denominator : ℝ)^5)

end MME.ReleasedGlobal


