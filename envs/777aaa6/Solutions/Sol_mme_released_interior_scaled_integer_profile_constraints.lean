-- Prove2me | solution 1 for mme_released_interior_scaled_integer_profile_constraints
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:34:29.802124+00:00
-- url     : https://prove2.me/submissions/76295153-ceae-42c2-a8e2-77ada0376860

import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_released_global_profile_data
import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
import Mathlib.Data.List.Sort

set_option autoImplicit false
namespace MME.ReleasedInterior
open MoreAsymmetryExactSeed

/-- The source recipe before the owner's coordinate permutation. -/
def seed_L (owner : Fin 6) (s : Fin 45) : Term :=
  ([owner0, owner1, owner2, owner3, owner4, owner5].getD owner.val []).getD
    (ReleasedGlobal.sourceIndex owner s).val ⟨[], [], [], [], [], [], []⟩

def role_L : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]]

/-- Two elementary triples form a square child_L with the specified grade. -/
def childSupport_L (shape : List ℕ) : List ℕ :=
  (List.range 36).filter fun a =>
    List.ofFn (fun i : Fin 3 =>
      (ReleasedGlobal.elementary ⟨a % 6, Nat.mod_lt _ (by decide)⟩ i).val +
      (ReleasedGlobal.elementary ⟨a / 6 % 6, Nat.mod_lt _ (by decide)⟩ i).val) == shape

/-- Exact child_L counts, including the three-atom boundary distributions and
all coordinate placements of the four-atom interior distribution. -/
def child_L (t : Term) (j : ℕ) (shape : List ℕ) : List (ℕ × ℕ) :=
  let p := ((t.children.find? (fun c => c.1 == j && c.2.1 == shape)).getD
    (0, [], 0)).2.2
  let support := childSupport_L shape
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

/-- Re-encode an elementary triple after applying the owner's role_L order. -/
def permElementary_L (owner : Fin 6) (a : Fin 6) : ℕ :=
  ((List.range 6).find? fun b =>
    List.ofFn (fun i : Fin 3 => ReleasedGlobal.elementary
      ⟨b % 6, Nat.mod_lt _ (by decide)⟩ i) ==
    List.ofFn (fun i : Fin 3 => ReleasedGlobal.elementary a (role_L owner i))).getD 0

def permAtom_L (owner : Fin 6) (a : ℕ) : ℕ :=
  ((List.range 4).map fun h =>
    permElementary_L owner ⟨a / 6 ^ h % 6, Nat.mod_lt _ (by decide)⟩ * 6 ^ h).sum

/-- Region weight times split weight times independent left and right child_L
counts. The owner permutation is applied to the actual elementary atoms. -/
def contributions_L (owner : Fin 6) (s : Fin 45) : List (ℕ × ℕ) :=
  let t := seed_L owner s
  (List.range 6).flatMap fun j =>
    t.splits.zipIdx |>.flatMap fun (shape, k) =>
      let complement := t.shape.zipWith (· - ·) shape
      (child_L t j shape).flatMap fun (a, x) =>
        (child_L t j complement).map fun (b, y) =>
          (permAtom_L owner (a + 36 * b),
            t.region.getD j 0 * (t.alpha.getD j []).getD k 0 * x * y)

/-- Combine repeated atoms, discard zero weights, and sort by atom index. -/
def reconstructed_L (owner : Fin 6) (s : Fin 45) : List (ℕ × ℕ) :=
  let entries := (contributions_L owner s).filter fun p => p.2 != 0
  ((entries.map Prod.fst).eraseDups.insertionSort (· ≤ ·)).map fun a =>
    (a, ((entries.filter (fun p => p.1 == a)).map Prod.snd).sum)


open BigOperators MME.RecursiveYZ MME.CompleteSplit

/-- Every region has the actual grade of its released global component. -/
def parent_L (s : Fin 45) : Fin 6 → Fin 3 → ℕ :=
  fun _ i => ((ReleasedGlobal.shape s).val i).val

theorem parent_total_L (s : Fin 45) (r : Fin 6) :
    parent_L s r 0 + parent_L s r 1 + parent_L s r 2 = 2 * 4 :=
  (ReleasedGlobal.shape s).property.1

abbrev Split_L (s : Fin 45) := RecursiveThinSplit.Split 4 (parent_L s 0)

def inverseRole_L : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![2,0,1], ![1,2,0], ![2,1,0]]

private theorem inverse_role_apply_L : ∀ (owner : Fin 6) (i : Fin 3),
    inverseRole_L owner (role_L owner i) = i := by decide +kernel

/-- Express an actual child_L grade in the source recipe's coordinate order. -/
def sourceShape_L (owner : Fin 6) {s : Fin 45} (c : Split_L s) : List ℕ :=
  List.ofFn (fun i => (c.val (inverseRole_L owner i)).val)

def splitWeight_L (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split_L s) : ℕ :=
  ((seed_L owner s).alpha.getD r.val []).getD
    ((seed_L owner s).splits.idxOf (sourceShape_L owner c)) 0

def regionalSize_L (owner : Fin 6) (s : Fin 45) (r : Fin 6) : ℕ :=
  (seed_L owner s).region.getD r.val 0 * denominator ^ 3

def splitCount_L (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split_L s) : ℕ :=
  (seed_L owner s).region.getD r.val 0 * splitWeight_L owner s r c * denominator ^ 2

/-- Apply the owner permutation to the mode of each square-child_L word. -/
def childWord_L (owner : Fin 6) (a : ℕ) (i : Fin 3) : CompleteWord 2 :=
  fun h => ReleasedGlobal.elementary
    ⟨a / 6 ^ h.val % 6, Nat.mod_lt _ (by decide)⟩ (role_L owner i)

def childMarginal_L (owner : Fin 6) (s : Fin 45) (r : Fin 6)
    (c : Split_L s) (i : Fin 3) (w : CompleteWord 2) : ℕ :=
  ((child_L (seed_L owner s) r.val (sourceShape_L owner c)).map
    (fun p => if childWord_L owner p.1 i = w then p.2 else 0)).sum

/-- Integer counts for both complementary occurrences of the same child_L cell. -/
def integerProfile_L (owner : Fin 6) (s : Fin 45) (i : Fin 3)
    (c : Cell 4 6 (parent_L s)) (w : CompleteWord 2) : ℕ :=
  (seed_L owner s).region.getD c.1.val 0 *
    (splitWeight_L owner s c.1 c.2 +
      splitWeight_L owner s c.1 (complement (parent_total_L s c.1) c.2)) *
    denominator * childMarginal_L owner s c.1 c.2 i w

end MME.ReleasedInterior


set_option autoImplicit false
namespace MME.ReleasedInterior
open MoreAsymmetryExactSeed



/-- Every square-child_L distribution used by an interior released recipe has
exact mass equal to the common denominator, including children in zero-weight
regions. Complementary splits occur in the same split list. -/
private theorem mme_released_interior_child_mass (owner : Fin 6) (s : Fin 45) :
    (seed_L owner s).boundary = [] →
      ∀ (j : Fin 6) (shape : List ℕ), shape ∈ (seed_L owner s).splits →
        ((child_L (seed_L owner s) j.val shape).map Prod.snd).sum = denominator := by
  fin_cases owner
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

open BigOperators MME.RecursiveYZ MME.CompleteSplit




private theorem source_shape_mem (owner : Fin 6) (s : Fin 45) :
    (seed_L owner s).boundary = [] →
      ∀ c : Split_L s, sourceShape_L owner c ∈ (seed_L owner s).splits := by
  fin_cases owner
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

private theorem marginal_mass (owner : Fin 6) (L : List (ℕ × ℕ)) (i : Fin 3) :
    (∑ w : CompleteWord 2,
      (L.map (fun a => if childWord_L owner a.1 i = w then a.2 else 0)).sum) =
      (L.map Prod.snd).sum := by
  classical
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]
    simp

/-- The actual integer child_L profiles have the exact mass of the two
complementary child_L occurrences, for every released interior component. -/
private theorem mme_released_interior_integer_profile_mass
    (owner : Fin 6) (s : Fin 45) (hi : (seed_L owner s).boundary = [])
    (i : Fin 3) (c : Cell 4 6 (parent_L s)) :
    ∑ w, integerProfile_L owner s i c w =
      splitCount_L owner s c.1 c.2 +
        splitCount_L owner s c.1 (complement (parent_total_L s c.1) c.2) := by
  simp only [integerProfile_L, childMarginal_L, ← Finset.mul_sum, marginal_mass]
  rw [mme_released_interior_child_mass owner s hi c.1 _
    (source_shape_mem owner s hi c.2)]
  simp only [splitCount_L]
  ring

private theorem child_mem_grade (t : Term) (j : ℕ) (shape : List ℕ)
    (p : ℕ × ℕ) (hp : p ∈ child_L t j shape) :
    List.ofFn (fun i : Fin 3 =>
      (ReleasedGlobal.elementary ⟨p.1 % 6, Nat.mod_lt _ (by decide)⟩ i).val +
      (ReleasedGlobal.elementary ⟨p.1 / 6 % 6, Nat.mod_lt _ (by decide)⟩ i).val) = shape := by
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hp
  have hfst : a = p.1 := congrArg Prod.fst heq
  have hgrade := (List.mem_filter.mp ha).2
  simpa only [hfst, beq_iff_eq] using hgrade

private theorem child_word_grade (owner : Fin 6) (s : Fin 45) (r : Fin 6)
    (c : Split_L s) (p : ℕ × ℕ)
    (hp : p ∈ child_L (seed_L owner s) r.val (sourceShape_L owner c)) (i : Fin 3) :
    ∑ h, (childWord_L owner p.1 i h).val = (c.val i).val := by
  have h := child_mem_grade _ _ _ p hp
  unfold sourceShape_L at h
  have hvec := List.ofFn_injective h
  have hi := congrFun hvec (role_L owner i)
  change (∑ h : Fin 2, (childWord_L owner p.1 i h).val) = (c.val i).val
  rw [Fin.sum_univ_two]
  simpa only [inverse_role_apply_L, childWord_L,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, Nat.div_one] using hi

/-- Positive child_L counts have the actual child_L grade after applying the
owner's coordinate permutation. This includes all supported interior shapes. -/
private theorem mme_released_interior_integer_profile_support
    (owner : Fin 6) (s : Fin 45) (i : Fin 3)
    (c : Cell 4 6 (parent_L s)) (w : CompleteWord 2)
    (hw : 0 < integerProfile_L owner s i c w) :
    ∑ h, (w h).val = (c.2.val i).val := by
  by_contra hn
  have hz : childMarginal_L owner s c.1 c.2 i w = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have hne : childWord_L owner a.1 i ≠ w := by
      intro heq
      exact hn (heq ▸ child_word_grade owner s c.1 c.2 a ha i)
    simp only [if_neg hne]
  simp only [integerProfile_L, hz, mul_zero] at hw
  exact (Nat.lt_irrefl 0) hw


private theorem child_mem_lt (t : Term) (j : ℕ) (shape : List ℕ)
    (p : ℕ × ℕ) (hp : p ∈ child_L t j shape) : p.1 < 36 := by
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp hp
  have hfst : a = p.1 := congrArg Prod.fst heq
  have h := List.mem_range.mp (List.mem_filter.mp ha).1
  simpa only [hfst] using h

private theorem child_atomic_boundary : ∀ (owner : Fin 6) (a : Fin 36),
    ((∑ h, (childWord_L owner a.val 2 h).val) = 0 →
      childWord_L owner a.val 1 = fun h => Fin.rev (childWord_L owner a.val 0 h)) ∧
    ((∑ h, (childWord_L owner a.val 0 h).val) = 0 →
      childWord_L owner a.val 2 = fun h => Fin.rev (childWord_L owner a.val 1 h)) ∧
    ((∑ h, (childWord_L owner a.val 1 h).val) = 0 →
      childWord_L owner a.val 2 = fun h => Fin.rev (childWord_L owner a.val 0 h)) := by
  decide +kernel

private theorem marginal_reverse (owner : Fin 6) (L : List (ℕ × ℕ)) (i j : Fin 3)
    (h : ∀ a ∈ L, childWord_L owner a.1 i = fun r => Fin.rev (childWord_L owner a.1 j r))
    (w : CompleteWord 2) :
    (L.map (fun a => if childWord_L owner a.1 i = w then a.2 else 0)).sum =
      (L.map (fun a => if childWord_L owner a.1 j = (fun r => Fin.rev (w r)) then a.2 else 0)).sum := by
  classical
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have heq : childWord_L owner a.1 i = w ↔
      childWord_L owner a.1 j = (fun r => Fin.rev (w r)) := by
    rw [h a ha]
    constructor
    · intro hw
      funext r
      have hh := congrArg (fun f => Fin.rev (f r)) hw
      simpa using hh
    · intro hw
      funext r
      simp only [hw, Fin.rev_rev]
  simp only [heq]

/-- Boundary child_L counts satisfy the complementary-word identities for all
owners and all three choices of the zero coordinate. -/
private theorem mme_released_interior_integer_profile_boundary (owner : Fin 6) (s : Fin 45) :
    BoundaryProfiles (integerProfile_L owner s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hz w
    simp only [integerProfile_L]
    congr 1
    unfold childMarginal_L
    apply marginal_reverse
    intro a ha
    exact (child_atomic_boundary owner ⟨a.1, child_mem_lt _ _ _ a ha⟩).1
      ((child_word_grade owner s c.1 c.2 a ha 2).trans hz)
  · intro c hz w
    simp only [integerProfile_L]
    congr 1
    unfold childMarginal_L
    apply marginal_reverse
    intro a ha
    exact (child_atomic_boundary owner ⟨a.1, child_mem_lt _ _ _ a ha⟩).2.1
      ((child_word_grade owner s c.1 c.2 a ha 0).trans hz)
  · intro c hz w
    simp only [integerProfile_L]
    congr 1
    unfold childMarginal_L
    apply marginal_reverse
    intro a ha
    exact (child_atomic_boundary owner ⟨a.1, child_mem_lt _ _ _ a ha⟩).2.2
      ((child_word_grade owner s c.1 c.2 a ha 1).trans hz)


/-- Regional split counts exhaust the corresponding parent_L occurrences;
zero-weight regions have zero counts throughout. -/
private theorem mme_released_interior_regional_split_mass (owner : Fin 6) (s : Fin 45) :
    (seed_L owner s).boundary = [] → ∀ r : Fin 6,
      ∑ c : Split_L s, splitCount_L owner s r c = regionalSize_L owner s r := by
  fin_cases owner
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

/-- The six region sizes sum to the released parent_L replication unit. -/
private theorem mme_released_interior_regional_total (owner : Fin 6) (s : Fin 45) :
    (seed_L owner s).boundary = [] →
      ∑ r : Fin 6, regionalSize_L owner s r = denominator ^ 4 := by
  fin_cases owner
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · fin_cases s
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel

private theorem mme_regional_reference_exists_iff_mass
    {half R : ℕ} {parent_L : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent_L r) → ℕ) :
    (∃ a : Address half R parent_L n, a ∈ RecursiveXHash.target m) ↔
      ∀ r, ∑ c, m r c = n r := by
  classical
  constructor
  · rintro ⟨a, ha⟩ r
    have hc := (Finset.mem_filter.mp ha).2 r
    change ∀ c, RecursiveThinSplit.count (a r) c = m r c at hc
    have hsum := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin (n r))) Finset.univ (a r)
    simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ,
      Fintype.card_fin] at hsum
    change (∑ c, RecursiveThinSplit.count (a r) c) = n r at hsum
    simpa only [hc] using hsum
  · intro hmass
    let e (r : Fin R) : Fin (n r) ≃ Σ c, Fin (m r c) :=
      Fintype.equivOfCardEq (by
        rw [Fintype.card_fin, Fintype.card_sigma]
        simpa only [Fintype.card_fin] using (hmass r).symm)
    let a : Address half R parent_L n := fun r t => (e r t).1
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro r c
    rw [RecursiveThinSplit.count, ← Fintype.card_subtype]
    let ef : {t : Fin (n r) // a r t = c} ≃
        {p : (Σ c, Fin (m r c)) // p.1 = c} :=
      Equiv.subtypeEquiv (e r) (fun _ => Iff.rfl)
    rw [Fintype.card_congr ef, Fintype.card_congr (Equiv.sigmaSubtype c),
      Fintype.card_fin]

end MME.ReleasedInterior
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

/-- Every positive replication of a released interior recipe supplies actual
integer profiles and a reference assignment satisfying the structural hypotheses
of the regional extraction theorem, with empty regions allowed. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed_L owner s).boundary = [])
    (k : ℕ) (hk : 0 < k) :
    let n := fun r => k * regionalSize_L owner s r
    let m := fun r c => k * splitCount_L owner s r c
    let mu := fun i c w => k * integerProfile_L owner s i c w
    ∃ reference : Address 4 6 (parent_L s) n,
      reference ∈ RecursiveXHash.target m ∧
      (∑ r : Fin 6, n r) = k * denominator ^ 4 ∧
      (∀ i c, ∑ w, mu i c w =
        m c.1 c.2 + m c.1 (complement (parent_total_L s c.1) c.2)) ∧
      (∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val) ∧
      BoundaryProfiles mu ∧
      0 < k * denominator ^ 2 ∧
      (∀ r, n r ≠ 0 → k * denominator ^ 2 ≤ n r) ∧
      (∀ r c, k * denominator ^ 2 ∣ m r c) := by
  classical
  dsimp only
  have hcounts (r : Fin 6) :
      (∑ c : Split_L s, k * splitCount_L owner s r c) = k * regionalSize_L owner s r := by
    rw [← Finset.mul_sum, mme_released_interior_regional_split_mass owner s hi r]
  obtain ⟨reference, href⟩ :=
    (mme_regional_reference_exists_iff_mass
      (fun r c => k * splitCount_L owner s r c)).mpr hcounts
  refine ⟨reference, href, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum, mme_released_interior_regional_total owner s hi]
  · intro i c
    rw [← Finset.mul_sum, mme_released_interior_integer_profile_mass owner s hi,
      Nat.mul_add]
  · intro i c w hw
    exact mme_released_interior_integer_profile_support owner s i c w
      (Nat.pos_of_mul_pos_left hw)
  · have hb := mme_released_interior_integer_profile_boundary owner s
    refine ⟨?_, ?_, ?_⟩
    · intro c hz w
      exact congrArg (k * ·) (hb.1 c hz w)
    · intro c hz w
      exact congrArg (k * ·) (hb.2.1 c hz w)
    · intro c hz w
      exact congrArg (k * ·) (hb.2.2 c hz w)
  · exact Nat.mul_pos hk (by norm_num [denominator])
  · intro r hn
    have hregion : 0 < (seed_L owner s).region.getD r.val 0 := by
      by_contra h
      have hz : (seed_L owner s).region.getD r.val 0 = 0 := by omega
      apply hn
      simp only [regionalSize_L, hz, zero_mul, mul_zero]
    have hlarge : denominator ^ 3 ≤ regionalSize_L owner s r := by
      unfold regionalSize_L
      calc denominator ^ 3 = 1 * denominator ^ 3 := (one_mul _).symm
        _ ≤ _ := Nat.mul_le_mul_right _ hregion
    exact Nat.mul_le_mul_left k
      ((show denominator ^ 2 ≤ denominator ^ 3 by norm_num [denominator]).trans hlarge)
  · intro r c
    exact Nat.mul_dvd_mul_left k (dvd_mul_left _ _)



