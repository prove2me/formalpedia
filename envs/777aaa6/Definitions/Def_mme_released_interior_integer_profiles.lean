-- Prove2me | Definitions.Def_mme_released_interior_integer_profiles
-- name    : mme_released_interior_integer_profiles
-- status  : Definition
-- author  : @Robertboy18
-- created : 2026-09-23T04:10:12.379931+00:00
-- url     : https://prove2.me/theorems/ff7f8214-c046-41fc-a1b6-954617853158
-- title:
--   Released interior reconstruction and integer child profiles
-- statement:
--   Exact definitions for all six owners of the released interior recipes: independent child reconstruction, owner permutations, regional split counts, child marginals, and integer profiles for complementary child occurrences. These definitions retain zero-sized regions and the released denominator. No extraction or matrix exponent bound is asserted.

import Definitions.Def_mme_recursive_region_parent_profiles
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


open BigOperators MME.RecursiveYZ MME.CompleteSplit

/-- Every region has the actual grade of its released global component. -/
def parent (s : Fin 45) : Fin 6 → Fin 3 → ℕ :=
  fun _ i => ((ReleasedGlobal.shape s).val i).val

theorem parent_total (s : Fin 45) (r : Fin 6) :
    parent s r 0 + parent s r 1 + parent s r 2 = 2 * 4 :=
  (ReleasedGlobal.shape s).property.1

abbrev Split (s : Fin 45) := RecursiveThinSplit.Split 4 (parent s 0)

def inverseRole : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![2,0,1], ![1,2,0], ![2,1,0]]

private theorem inverse_role_apply : ∀ (owner : Fin 6) (i : Fin 3),
    inverseRole owner (role owner i) = i := by decide +kernel

/-- Express an actual child grade in the source recipe's coordinate order. -/
def sourceShape (owner : Fin 6) {s : Fin 45} (c : Split s) : List ℕ :=
  List.ofFn (fun i => (c.val (inverseRole owner i)).val)

def splitWeight (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) : ℕ :=
  ((seed owner s).alpha.getD r.val []).getD
    ((seed owner s).splits.idxOf (sourceShape owner c)) 0

def regionalSize (owner : Fin 6) (s : Fin 45) (r : Fin 6) : ℕ :=
  (seed owner s).region.getD r.val 0 * denominator ^ 3

def splitCount (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) : ℕ :=
  (seed owner s).region.getD r.val 0 * splitWeight owner s r c * denominator ^ 2

/-- Apply the owner permutation to the mode of each square-child word. -/
def childWord (owner : Fin 6) (a : ℕ) (i : Fin 3) : CompleteWord 2 :=
  fun h => ReleasedGlobal.elementary
    ⟨a / 6 ^ h.val % 6, Nat.mod_lt _ (by decide)⟩ (role owner i)

def childMarginal (owner : Fin 6) (s : Fin 45) (r : Fin 6)
    (c : Split s) (i : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((child (seed owner s) r.val (sourceShape owner c)).map
    (fun p => if childWord owner p.1 i = w then p.2 else 0)).sum

/-- Integer counts for both complementary occurrences of the same child cell. -/
def integerProfile (owner : Fin 6) (s : Fin 45) (i : Fin 3)
    (c : Cell 4 6 (parent s)) (w : CompleteWord 2) : ℕ :=
  (seed owner s).region.getD c.1.val 0 *
    (splitWeight owner s c.1 c.2 +
      splitWeight owner s c.1 (complement (parent_total s c.1) c.2)) *
    denominator * childMarginal owner s c.1 c.2 i w

end MME.ReleasedInterior


