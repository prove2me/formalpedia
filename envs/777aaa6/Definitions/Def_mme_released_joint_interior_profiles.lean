-- Prove2me | Definitions.Def_mme_released_joint_interior_profiles
-- name    : mme_released_joint_interior_profiles
-- status  : Definition
-- author  : @Robertboy18
-- created : 2026-09-23T09:40:25.111008+00:00
-- url     : https://prove2.me/theorems/3d489536-019f-46c1-b6c3-52ee24f948d0
-- title:
--   Common inner profiles across all released owners
-- statement:
--   Exact integer profiles on 270 owner and parent labels, transported to one common inner orientation. Boundary-only labels have zero size. No source transport or exponent bound is asserted.

import Definitions.Def_mme_recursive_split_coordinate_data
import Definitions.Def_mme_released_interior_integer_profiles

namespace MME.ReleasedJointInterior

/-- One global owner and one of its 45 actual parent grades. -/
def component (j : Fin 270) : Fin 6 × Fin 45 := finProdFinEquiv.symm j

/-- The released convention for the six possible mode orders. -/
def roleEquiv (r : Fin 6) : Equiv.Perm (Fin 3) where
  toFun := ReleasedInterior.role r
  invFun := ReleasedInterior.inverseRole r
  left_inv := (by decide +kernel : ∀ (r : Fin 6) (i : Fin 3),
    ReleasedInterior.inverseRole r (ReleasedInterior.role r i) = i) r
  right_inv := (by decide +kernel : ∀ (r : Fin 6) (i : Fin 3),
    ReleasedInterior.role r (ReleasedInterior.inverseRole r i) = i) r

/-- Express an inner region's modes in the already permuted coordinates of an
outer owner. Each outer tensor is first returned to the common source order. -/
def orientation (owner r : Fin 6) : Equiv.Perm (Fin 3) :=
  (roleEquiv r).trans (roleEquiv owner).symm

def parent (r : Fin 6) (j : Fin 270) (i : Fin 3) : ℕ :=
  ReleasedInterior.parent (component j).2 0 (orientation (component j).1 r i)

theorem parent_total (r : Fin 6) (j : Fin 270) :
    parent r j 0 + parent r j 1 + parent r j 2 = 2 * 4 :=
  RecursiveThinSplit.coordinate_total
    (ReleasedInterior.parent_total (component j).2 0) (orientation (component j).1 r)

/-- Boundary parents have a separate direct matrix extraction. They remain as
zero-sized labels here, so all joint regions use the same component index. -/
def weight (j : Fin 270) : ℕ :=
  if (ReleasedInterior.seed (component j).1 (component j).2).boundary = [] then
    ReleasedGlobal.alpha (component j).1 (component j).2 else 0

def size (r : Fin 6) (k : ℕ) (j : Fin 270) : ℕ :=
  k * weight j * ReleasedInterior.regionalSize (component j).1 (component j).2 r

def splitEquiv (r : Fin 6) (j : Fin 270) :
    ReleasedInterior.Split (component j).2 ≃ RecursiveThinSplit.Split 4 (parent r j) :=
  RecursiveThinSplit.coordinateEquiv (ReleasedInterior.parent (component j).2 0)
    (orientation (component j).1 r)

def splitCount (r : Fin 6) (k : ℕ) (j : Fin 270)
    (c : RecursiveThinSplit.Split 4 (parent r j)) : ℕ :=
  k * weight j *
    ReleasedInterior.splitCount (component j).1 (component j).2 r ((splitEquiv r j).symm c)

/-- Physical square-child counts from all owners and parent grades, in one
common hashing orientation for inner region `r`. -/
def integerProfile (r : Fin 6) (k : ℕ) (i : Fin 3)
    (c : RecursiveYZ.Cell 4 270 (parent r)) (w : CompleteSplit.CompleteWord 2) : ℕ :=
  k * weight c.1 *
    ReleasedInterior.integerProfile (component c.1).1 (component c.1).2
      (orientation (component c.1).1 r i) ⟨r, (splitEquiv r c.1).symm c.2⟩ w

end MME.ReleasedJointInterior


