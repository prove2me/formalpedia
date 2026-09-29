-- Prove2me | Definitions.Def_mme_logarithmic_regional_CW_recipe
-- name    : mme_logarithmic_regional_CW_recipe
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-21T20:04:12.965728+00:00
-- url     : https://prove2.me/theorems/352619eb-faa7-4c20-af23-921b39b8ab94
-- title:
--   Regional recipes specified by explicit logarithmic loss budgets
-- statement:
--   A finite recursive recipe with actual integer regional profiles, source inclusions, unique type covers, region partitions, rotations, and boundary tensor identifications. At each descent the guaranteed nonnegative logarithmic rate is bounded by the explicit certifiedLogCopies formula of every type. logOutputs adds rates under descent and across tensor-product regions. inputs records type-cover costs exactly. No tensor restriction or copy-count conclusion is assumed; a separate compiler proves them.
-- source:
--   Derived from the proved regional entropy copy bound; More Asymmetry, arXiv:2404.16349v2, recursive hashing and hole repair.

import Definitions.Def_mme_regional_certified_log_copy_bound
open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RecursiveYZ.CWCells
set_option autoImplicit false
namespace MME.RegionRealization

/-- A regional recipe whose copy guarantee is an additive, fully explicit
logarithmic budget. The extraction steps still contain actual integer profiles,
source inclusions, unique covers, and boundary identifications. -/
inductive LogRecipe : (N ell : ℕ) → Predicate N → Type
  | boundary {N ell P} (data : BoundaryEnd ell N P) : LogRecipe N ell P
  | descend {N ell lower : ℕ} {P Q : Predicate N}
      (level_decreases : lower < ell) (types : ℕ) (rate : ℝ)
      (rate_nonneg : 0 ≤ rate)
      (steps : Fin types → IntegerStep lower N P)
      (budget : ∀ j, rate ≤ (steps j).certifiedLogCopies)
      (inside : ∀ j i x, (steps j).output i x → Q i x)
      (cover : ∀ x : Fin 3 → FineWord N, supported x → (∀ i, Q i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i))
      (next : LogRecipe N lower Q) : LogRecipe N ell P
  | partition {N ell parts : ℕ} {P : Predicate N}
      (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (Q : ∀ j, Predicate (size j))
      (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (children : ∀ j, LogRecipe (size j) ell (Q j)) : LogRecipe N ell P
  | rotate {N ell P} (child : LogRecipe N ell P) :
      LogRecipe N ell (fun i ↦ P (cyclicPerm.symm i))
  | swap {N ell P} (child : LogRecipe N ell P) :
      LogRecipe N ell (fun i ↦ P (swapFirstTwoPerm.symm i))

def LogRecipe.inputs {N ell : ℕ} {P : Predicate N} : LogRecipe N ell P → ℕ
  | .boundary _ => 1
  | .descend _ types _ _ _ _ _ _ next => types * next.inputs
  | .partition _ _ _ _ children => ∏ j, (children j).inputs
  | .rotate D => D.inputs
  | .swap D => D.inputs

noncomputable def LogRecipe.logOutputs {N ell : ℕ} {P : Predicate N} : LogRecipe N ell P → ℝ
  | .boundary _ => 0
  | .descend _ _ rate _ _ _ _ _ next => rate + next.logOutputs
  | .partition _ _ _ _ children => ∑ j, (children j).logOutputs
  | .rotate D => D.logOutputs
  | .swap D => D.logOutputs

def LogRecipe.dims {N ell : ℕ} {P : Predicate N} : LogRecipe N ell P → ℕ × ℕ × ℕ
  | .boundary D => (D.a,D.b,D.c)
  | .descend _ _ _ _ _ _ _ _ next => next.dims
  | .partition _ _ _ _ children =>
      (∏ j, (children j).dims.1, ∏ j, (children j).dims.2.1, ∏ j, (children j).dims.2.2)
  | .rotate D => (D.dims.2.2, D.dims.1, D.dims.2.1)
  | .swap D => (D.dims.2.2, D.dims.2.1, D.dims.1)

def LogRecipe.a {N ell : ℕ} {P : Predicate N} (D : LogRecipe N ell P) : ℕ := D.dims.1
def LogRecipe.b {N ell : ℕ} {P : Predicate N} (D : LogRecipe N ell P) : ℕ := D.dims.2.1
def LogRecipe.c {N ell : ℕ} {P : Predicate N} (D : LogRecipe N ell P) : ℕ := D.dims.2.2

end MME.RegionRealization


