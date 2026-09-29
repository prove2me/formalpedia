-- Prove2me | Theorems.Thm_mme_released_interior_regional_joint_counts
-- name    : mme_released_interior_regional_joint_counts
-- status  : Open
-- author  : @Robertboy18
-- created : 2026-09-23T03:32:40.048994+00:00
-- url     : https://prove2.me/theorems/b9ca64b6-eb3e-4f7e-8afd-cadce3b19447
-- title:
--   Exact regional reconstruction of every released interior component
-- statement:
--   For all six owners and every interior component of the released profile, its entire joint-count row equals the sum of region-weighted split distributions and independent square-child products, after the owner coordinate permutation. Counts are exact integers at denominator^4 scale. Zero-weight regions contribute zero. This establishes data reconstruction only; it does not assert a tensor extraction or an exponent bound.
-- source:
--   Released exact profile seed and released global joint counts; all 126 interior rows.

import Definitions.Def_mme_released_global_profile_data
import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
import Mathlib.Data.List.Sort

set_option autoImplicit false
namespace MME.ReleasedInterior
open MoreAsymmetryExactSeed

/-- The source recipe before the owner's coordinate permutation. -/
def seed (owner : Fin 6) (s : Fin 45) : Term :=
  ([owner0, owner1, owner2, owner3, owner4, owner5].getD owner.val []).getD
    (ReleasedGlobal.sourceIndex owner s).val ⟨[], [], [], [], [], [], []⟩

def role : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]]

/-- Two elementary triples form a square child with the specified grade. -/
def childSupport (shape : List ℕ) : List ℕ :=
  (List.range 36).filter fun a =>
    List.ofFn (fun i : Fin 3 =>
      (ReleasedGlobal.elementary ⟨a % 6, Nat.mod_lt _ (by decide)⟩ i).val +
      (ReleasedGlobal.elementary ⟨a / 6 % 6, Nat.mod_lt _ (by decide)⟩ i).val) == shape

/-- Exact child counts, including the three-atom boundary distributions and
all coordinate placements of the four-atom interior distribution. -/
def child (t : Term) (j : ℕ) (shape : List ℕ) : List (ℕ × ℕ) :=
  let p := ((t.children.find? (fun c => c.1 == j && c.2.1 == shape)).getD
    (0, [], 0)).2.2
  let support := childSupport shape
  support.map fun a => (a,
    if support.length = 1 then denominator
    else if support.length = 2 then denominator / 2
    else if support.length = 3 then
      if a % 6 = a / 6 then denominator - 2 * p else p
    else if (List.range 3).any (fun i => shape.getD i 0 == 2 &&
        ((ReleasedGlobal.elementary ⟨a % 6, Nat.mod_lt _ (by decide)⟩
            ⟨i % 3, Nat.mod_lt _ (by decide)⟩).val == 2 ||
         (ReleasedGlobal.elementary ⟨a / 6 % 6, Nat.mod_lt _ (by decide)⟩
            ⟨i % 3, Nat.mod_lt _ (by decide)⟩).val == 2))
      then p else denominator / 2 - p)

/-- Re-encode an elementary triple after applying the owner's role order. -/
def permElementary (owner : Fin 6) (a : Fin 6) : ℕ :=
  ((List.range 6).find? fun b =>
    List.ofFn (fun i : Fin 3 => ReleasedGlobal.elementary
      ⟨b % 6, Nat.mod_lt _ (by decide)⟩ i) ==
    List.ofFn (fun i : Fin 3 => ReleasedGlobal.elementary a (role owner i))).getD 0

def permAtom (owner : Fin 6) (a : ℕ) : ℕ :=
  ((List.range 4).map fun h =>
    permElementary owner ⟨a / 6 ^ h % 6, Nat.mod_lt _ (by decide)⟩ * 6 ^ h).sum

/-- Region weight times split weight times independent left and right child
counts. The owner permutation is applied to the actual elementary atoms. -/
def contributions (owner : Fin 6) (s : Fin 45) : List (ℕ × ℕ) :=
  let t := seed owner s
  (List.range 6).flatMap fun j =>
    t.splits.zipIdx |>.flatMap fun (shape, k) =>
      let complement := t.shape.zipWith (· - ·) shape
      (child t j shape).flatMap fun (a, x) =>
        (child t j complement).map fun (b, y) =>
          (permAtom owner (a + 36 * b),
            t.region.getD j 0 * (t.alpha.getD j []).getD k 0 * x * y)

/-- Combine repeated atoms, discard zero weights, and sort by atom index. -/
def reconstructed (owner : Fin 6) (s : Fin 45) : List (ℕ × ℕ) :=
  let entries := (contributions owner s).filter fun p => p.2 != 0
  ((entries.map Prod.fst).eraseDups.insertionSort (· ≤ ·)).map fun a =>
    (a, ((entries.filter (fun p => p.1 == a)).map Prod.snd).sum)


end MME.ReleasedInterior
open MME.ReleasedInterior MME

theorem mme_released_interior_regional_joint_counts (owner : Fin 6) (s : Fin 45) :
    (seed owner s).boundary = [] →
      reconstructed owner s =
        (ReleasedGlobal.jointRows owner s).map (fun p => (p.1.val, p.2)) := by sorry
