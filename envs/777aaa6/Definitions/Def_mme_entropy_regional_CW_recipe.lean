-- Prove2me | Definitions.Def_mme_entropy_regional_CW_recipe
-- name    : mme_entropy_regional_CW_recipe
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T21:16:45.767616+00:00
-- url     : https://prove2.me/theorems/0b48923b-4237-4298-a2fc-2fb10f2ab0f3
-- title:
--   Regional recipes with proved explicit entropy copy guarantees
-- statement:
--   Finite recipes use existing consistent integer regional steps, but count copies by the explicit summed-entropy lower formula and its finite hash, rounding and repair losses. Compilation to the existing IntegerRecipe is a separate proved theorem. No entropy estimate or tensor map is stored as a premise.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . The numerical surplus certificate remains Open.

import Definitions.Def_mme_regional_entropy_copy_bound
open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
namespace MME.RegionRealization

/-- Finite recipes with explicit regional entropy copy guarantees. No entropy rate,
prime, hash state, selected family, or tensor map is supplied as an assumption. -/
inductive EntropyRecipe : (N ell : ℕ) → Predicate N → Type
  | boundary {N ell P} (data : BoundaryEnd ell N P) : EntropyRecipe N ell P
  | descend {N ell lower : ℕ} {P Q : Predicate N}
      (level_decreases : lower < ell) (types copies : ℕ)
      (steps : Fin types → IntegerStep lower N P)
      (enough : ∀ j, copies ≤ (steps j).entropyCopies)
      (inside : ∀ j i x, (steps j).output i x → Q i x)
      (cover : ∀ x : Fin 3 → FineWord N, supported x → (∀ i, Q i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i))
      (next : EntropyRecipe N lower Q) : EntropyRecipe N ell P
  | partition {N ell parts : ℕ} {P : Predicate N}
      (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (Q : ∀ j, Predicate (size j))
      (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (children : ∀ j, EntropyRecipe (size j) ell (Q j)) : EntropyRecipe N ell P
  | rotate {N ell P} (child : EntropyRecipe N ell P) :
      EntropyRecipe N ell (fun i ↦ P (cyclicPerm.symm i))
  | swap {N ell P} (child : EntropyRecipe N ell P) :
      EntropyRecipe N ell (fun i ↦ P (swapFirstTwoPerm.symm i))

def EntropyRecipe.inputs {N ell : ℕ} {P : Predicate N} : EntropyRecipe N ell P → ℕ
  | .boundary _ => 1
  | .descend _ types _ _ _ _ _ next => types * next.inputs
  | .partition _ _ _ _ children => ∏ j, (children j).inputs
  | .rotate D => D.inputs
  | .swap D => D.inputs

def EntropyRecipe.outputs {N ell : ℕ} {P : Predicate N} : EntropyRecipe N ell P → ℕ
  | .boundary _ => 1
  | .descend _ _ copies _ _ _ _ next => copies * next.outputs
  | .partition _ _ _ _ children => ∏ j, (children j).outputs
  | .rotate D => D.outputs
  | .swap D => D.outputs

def EntropyRecipe.dims {N ell : ℕ} {P : Predicate N} : EntropyRecipe N ell P → ℕ × ℕ × ℕ
  | .boundary D => (D.a,D.b,D.c)
  | .descend _ _ _ _ _ _ _ next => next.dims
  | .partition _ _ _ _ children =>
      (∏ j, (children j).dims.1, ∏ j, (children j).dims.2.1, ∏ j, (children j).dims.2.2)
  | .rotate D => (D.dims.2.2, D.dims.1, D.dims.2.1)
  | .swap D => (D.dims.2.2, D.dims.2.1, D.dims.1)

def EntropyRecipe.a {N ell : ℕ} {P : Predicate N} (D : EntropyRecipe N ell P) : ℕ := D.dims.1
def EntropyRecipe.b {N ell : ℕ} {P : Predicate N} (D : EntropyRecipe N ell P) : ℕ := D.dims.2.1
def EntropyRecipe.c {N ell : ℕ} {P : Predicate N} (D : EntropyRecipe N ell P) : ℕ := D.dims.2.2

end MME.RegionRealization


