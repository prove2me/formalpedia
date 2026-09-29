-- Prove2me | Definitions.Def_mme_integer_regional_CW_recipe
-- name    : mme_integer_regional_CW_recipe
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T17:20:27.537339+00:00
-- url     : https://prove2.me/theorems/017477b6-3059-430f-9e83-13aac76dd601
-- title:
--   Integer regional recipes with computed extraction counts
-- statement:
--   A finite recursive regional recipe stores consistent integer profiles, the explicit polynomial size test and count-derived copy guarantees, with exact-type covers, coordinate partitions and mode rotations. It stores no prime, hash state, selected-address family, assumed hole fraction, assumed entropy rate, or tensor map. Compilation to the existing RegionalPlan is a separate theorem. Existence of a successful numerical recipe remains a separate obligation.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Definitions.Def_mme_recursive_regional_CW_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_region_hash_loads
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Semiring

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
namespace MME.RegionRealization

/-- Integer region inputs before any prime, hash state, isolated family, or
hole set is chosen. The scalar size test is explicit; hole bounds are derived. -/
structure IntegerStep (ell M : ℕ) (P : Predicate M) where
  half : ℕ
  R : ℕ
  parent : Fin R → Fin 3 → ℕ
  n : Fin R → ℕ
  total : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half
  half_eq : half = 2 * 2 ^ (ell - 1)
  m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ
  N : ℕ
  hashPositions : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)
  L : ℕ
  positions : Fin L ≃ Position n
  length : L * 2 ^ (ell - 1) = M
  mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ
  mass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (total c.1) c.2)
  support : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val
  boundary : BoundaryProfiles mu
  reference : Address half R parent n
  reference_target : reference ∈ RecursiveXHash.target m
  minimum : ℕ
  repairScale : ℕ
  minimum_pos : 0 < minimum
  repairScale_gt_one : 1 < repairScale
  parent_size : ∀ r, minimum ≤ n r
  split_divisible : ∀ r c, minimum ∣ m r c
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  size_test : (8 * repairScale : ℝ) *
    (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (minimum : ℝ) * epsilon ^ 2
  source_inside : ∀ i x, parentTypical total n m (mu i) epsilon
    (ProfiledCW.split positions length x) → P i x

noncomputable def IntegerStep.keep {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (i : Fin 2) (_ : Address D.half D.R D.parent D.n) :=
  parentTypical D.total D.n D.m (D.mu (yzMode i)) D.epsilon

noncomputable def IntegerStep.scale {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P) : ℕ :=
  commonScale D.half (loadNum D.total D.m D.repairScale (fun i ↦ D.mu (yzMode i)) D.keep) (loadDen D.m)

noncomputable def IntegerStep.capacity {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P) : ℕ :=
  ∏ i : Fin 3, Nat.card (Block ell (fullCell D.total D.reference) (fun c i ↦ (c.2.val i).val) D.mu i)

noncomputable def IntegerStep.repairExponent {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P) : ℕ :=
  Nat.log D.repairScale D.capacity + 1

noncomputable def IntegerStep.lower {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P) : ℝ :=
  ((RecursiveXHash.target (n := D.n) D.m).card : ℝ) *
    Real.exp (-4 * Real.sqrt (Real.log D.scale)) / (32 * D.scale)

/-- A guaranteed integer copy count, computed from the actual finite counts.
It is not a supplied entropy-rate or tensor-restriction assumption. -/
noncomputable def IntegerStep.copies {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P) : ℕ :=
  ⌊D.lower⌋₊ / 8 ^ D.repairExponent

def IntegerStep.output {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P) : Predicate M :=
  fun i x ↦ Graded D.total i D.reference (ProfiledCW.split D.positions D.length x) ∧
    Useful (fullCell D.total D.reference) (D.mu i) (ProfiledCW.split D.positions D.length x)

/-- A finite regional recipe whose extraction steps contain only integer
profiles and explicit count formulas. Compilation into actual hash stages and
an existing RegionalPlan is a separate proved theorem. -/
inductive IntegerRecipe : (N ell : ℕ) → Predicate N → Type
  | boundary {N ell P} (data : BoundaryEnd ell N P) : IntegerRecipe N ell P
  | descend {N ell lower : ℕ} {P Q : Predicate N}
      (level_decreases : lower < ell) (types copies : ℕ)
      (steps : Fin types → IntegerStep lower N P)
      (enough : ∀ j, copies ≤ (steps j).copies)
      (inside : ∀ j i x, (steps j).output i x → Q i x)
      (cover : ∀ x : Fin 3 → FineWord N, supported x → (∀ i, Q i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i))
      (next : IntegerRecipe N lower Q) : IntegerRecipe N ell P
  | partition {N ell parts : ℕ} {P : Predicate N}
      (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (Q : ∀ j, Predicate (size j))
      (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (children : ∀ j, IntegerRecipe (size j) ell (Q j)) : IntegerRecipe N ell P
  | rotate {N ell P} (child : IntegerRecipe N ell P) :
      IntegerRecipe N ell (fun i ↦ P (cyclicPerm.symm i))
  | swap {N ell P} (child : IntegerRecipe N ell P) :
      IntegerRecipe N ell (fun i ↦ P (swapFirstTwoPerm.symm i))

def IntegerRecipe.inputs {N ell : ℕ} {P : Predicate N} : IntegerRecipe N ell P → ℕ
  | .boundary _ => 1
  | .descend _ types _ _ _ _ _ next => types * next.inputs
  | .partition _ _ _ _ children => ∏ j, (children j).inputs
  | .rotate D => D.inputs
  | .swap D => D.inputs

def IntegerRecipe.outputs {N ell : ℕ} {P : Predicate N} : IntegerRecipe N ell P → ℕ
  | .boundary _ => 1
  | .descend _ _ copies _ _ _ _ next => copies * next.outputs
  | .partition _ _ _ _ children => ∏ j, (children j).outputs
  | .rotate D => D.outputs
  | .swap D => D.outputs

def IntegerRecipe.dims {N ell : ℕ} {P : Predicate N} : IntegerRecipe N ell P → ℕ × ℕ × ℕ
  | .boundary D => (D.a,D.b,D.c)
  | .descend _ _ _ _ _ _ _ next => next.dims
  | .partition _ _ _ _ children =>
      (∏ j, (children j).dims.1, ∏ j, (children j).dims.2.1, ∏ j, (children j).dims.2.2)
  | .rotate D => (D.dims.2.2, D.dims.1, D.dims.2.1)
  | .swap D => (D.dims.2.2, D.dims.2.1, D.dims.1)

def IntegerRecipe.a {N ell : ℕ} {P : Predicate N} (D : IntegerRecipe N ell P) : ℕ := D.dims.1
def IntegerRecipe.b {N ell : ℕ} {P : Predicate N} (D : IntegerRecipe N ell P) : ℕ := D.dims.2.1
def IntegerRecipe.c {N ell : ℕ} {P : Predicate N} (D : IntegerRecipe N ell P) : ℕ := D.dims.2.2

end MME.RegionRealization


