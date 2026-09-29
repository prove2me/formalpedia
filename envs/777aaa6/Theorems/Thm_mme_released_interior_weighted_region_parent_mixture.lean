-- Prove2me | Theorems.Thm_mme_released_interior_weighted_region_parent_mixture
-- name    : mme_released_interior_weighted_region_parent_mixture
-- status  : Open
-- author  : @Robertboy18
-- created : 2026-09-23T03:52:17.024556+00:00
-- url     : https://prove2.me/theorems/8cef580f-3e70-4f36-a013-7961d1e900ef
-- title:
--   Released interior parent mixtures equal weighted child products
-- statement:
--   For every released interior recipe, owner, region, mode and pair of child words, the regional parent mixture weighted by its region size equals the exact released alpha-weighted product of its child marginals at denominator-fourth-power scale. Empty regions contribute zero. In nonempty regions, the proof cancels the integer profile scale using kernel-checked positivity of every split alpha weight. This is a regional identity; the aggregate equality to the released global joint row and entropy-rate extraction remain separate obligations.
--
--   Superseded publication: the original submission failed in the platform target checker. The same mathematical result is verified in `mme_released_interior_weighted_region_parent_mixture_exact`, which imports the separately published interior definitions.
-- source:
--   Released exact profile seed, child marginal mass, positive interior split weights and normalization.

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
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_weighted_region_parent_mixture
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (r : Fin 6) (w : Fin 2 → CompleteWord 2) :
    ((regionalSize owner s r : ℝ) / (denominator : ℝ) ^ 4) *
      RegionRealization.parentMixture (parent_total s)
        (regionalSize owner s) (splitCount owner s) (integerProfile owner s i) r w =
    ((seed owner s).region.getD r.val 0 : ℝ) / (denominator : ℝ) ^ 4 *
      ∑ c : Split s, (splitWeight owner s r c : ℝ) *
        (childMarginal owner s r c i (w 0) : ℝ) *
        (childMarginal owner s r (complement (parent_total s r) c) i (w 1) : ℝ) := by sorry
