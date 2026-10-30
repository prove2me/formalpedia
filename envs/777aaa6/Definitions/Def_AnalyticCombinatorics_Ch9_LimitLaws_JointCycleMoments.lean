-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_JointCycleMoments
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_JointCycleMoments
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T18:44:04.021435+00:00
-- url     : https://prove2.me/theorems/20738833-6b15-4eb1-ab8f-806dab17b33c
-- title:
--   Fixed-point incidence objects for mixed cycle counts
-- statement:
--   On an arbitrary finite type, fixed vertices, their finite cardinality, permutations fixing a distinguished point, and two incidence sum types are explicit. Complement-permutation and incidence equivalences supply the finite counting objects for mixed factorial moments.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/JointCycleMoments.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Joint factorial moments for cycle counts

This file starts the mixed factorial-moment theory for cycle counts of
distinct lengths.  The banked result is the exact two-length identity for
nontrivial lengths.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace RCyclesPoissonNS
namespace JointCycleMomentsNS

section GeneralFinite

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Fixed points of a permutation on an arbitrary finite type. -/
abbrev FixedPointsOfPermIn (σ : Equiv.Perm α) : Type u :=
  Function.fixedPoints σ

/-- Fixed-point count on an arbitrary finite type. -/
def fixedPointCountIn (σ : Equiv.Perm α) : ℕ :=
  Fintype.card (FixedPointsOfPermIn (α := α) σ)

/-- Permutations fixing a distinguished point. -/
abbrev PermFixingPointIn (x : α) : Type u :=
  {σ : Equiv.Perm α // σ x = x}

instance instFintypePermFixingPointIn (x : α) : Fintype (PermFixingPointIn (α := α) x) := by
  classical
  unfold PermFixingPointIn
  infer_instance

/-- Count the same fixed-point incidence relation first by permutations. -/
abbrev FixedPointByPermIn : Type u :=
  Σ σ : Equiv.Perm α, FixedPointsOfPermIn (α := α) σ

/-- Count the same fixed-point incidence relation first by the distinguished
fixed point. -/
abbrev FixedPointByPointIn : Type u :=
  Σ x : α, PermFixingPointIn (α := α) x

def fixedPointByPermEquivByPointIn :
    FixedPointByPermIn (α := α) ≃ FixedPointByPointIn (α := α) where
  toFun x :=
    ⟨x.2.1, ⟨x.1, Function.mem_fixedPoints_iff.mp x.2.2⟩⟩
  invFun x :=
    ⟨x.2.1, ⟨x.1, Function.mem_fixedPoints_iff.mpr x.2.2⟩⟩
  left_inv := by
    rintro ⟨σ, x, hx⟩
    rfl
  right_inv := by
    rintro ⟨x, σ, hx⟩
    rfl

def permComplementEquivFixingPointIn (x : α) :
    Equiv.Perm {y : α // y ≠ x} ≃ PermFixingPointIn (α := α) x :=
  (Equiv.Perm.subtypeEquivSubtypePerm (fun y : α => y ≠ x)).trans
    { toFun := fun σ => ⟨σ.1, σ.2 x (by simp)⟩
      invFun := fun σ =>
        ⟨σ.1, by
          intro y hy
          have hyx : y = x := not_not.mp hy
          rw [hyx]
          exact σ.2⟩
      left_inv := by
        rintro ⟨σ, hσ⟩
        rfl
      right_inv := by
        rintro ⟨σ, hσ⟩
        rfl }

end GeneralFinite

end JointCycleMomentsNS
end RCyclesPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics


