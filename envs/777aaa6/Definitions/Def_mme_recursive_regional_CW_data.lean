-- Prove2me | Definitions.Def_mme_recursive_regional_CW_data
-- name    : mme_recursive_regional_CW_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T15:15:41.434557+00:00
-- url     : https://prove2.me/theorems/053f675c-5d86-4ce6-9bb3-2f39900c0c95
-- title:
--   Finite CW recursion with independent regions and all six mode roles
-- statement:
--   A finite RegionalPlan combines exact-profile interior descents, proved boundary endpoints, products over disjoint position regions, and cyclic or transposed mode roles. Every descent strictly decreases the level. Region children may independently recurse and change mode roles.
--
--   The computed input count charges every exact type cover; the output count retains every repaired copy. Regional products multiply both counts and all matrix dimensions.
--
--   The recipe contains finite combinatorial predicates and data only. It does not assume a tensor restriction or assert existence of a plan achieving a numerical exponent.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Theorems 6.2 and 6.4, Proposition 6.3. Finite constructive certificate interface with explicit type-cover source costs.

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_six_symmetrized_tau_value

open BigOperators MME MME.TensorObj
set_option autoImplicit false
namespace MME.ProfiledCW

/-- Finite recipes allowing joint descent, position regions, and all six mode roles.
Every constructor stores only finite combinatorial data, never a tensor map. -/
inductive RegionalPlan : (N ell : ℕ) → Predicate N → Type
  | base {N ell P} (data : Plan N ell P) : RegionalPlan N ell P
  | descend {N ell lower : ℕ} {P Q : Predicate N}
      (level_decreases : lower < ell)
      (types copies : ℕ)
      (steps : Fin types → ExactStep lower N P)
      (enough : ∀ j, copies ≤ (steps j).copies)
      (inside : ∀ j i x, (steps j).output i x → Q i x)
      (cover : ∀ x : Fin 3 → FineWord N, supported x → (∀ i, Q i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i))
      (next : RegionalPlan N lower Q) : RegionalPlan N ell P
  | partition {N ell parts : ℕ} {P : Predicate N}
      (size : Fin parts → ℕ)
      (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (Q : ∀ j, Predicate (size j))
      (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (children : ∀ j, RegionalPlan (size j) ell (Q j)) : RegionalPlan N ell P
  | rotate {N ell P} (child : RegionalPlan N ell P) :
      RegionalPlan N ell (fun i ↦ P (cyclicPerm.symm i))
  | swap {N ell P} (child : RegionalPlan N ell P) :
      RegionalPlan N ell (fun i ↦ P (swapFirstTwoPerm.symm i))

def RegionalPlan.inputs {N ell : ℕ} {P : Predicate N} : RegionalPlan N ell P → ℕ
  | .base D => D.inputs
  | .descend _ types _ _ _ _ _ next => types * next.inputs
  | .partition _ _ _ _ children => ∏ j, (children j).inputs
  | .rotate D => D.inputs
  | .swap D => D.inputs

def RegionalPlan.outputs {N ell : ℕ} {P : Predicate N} : RegionalPlan N ell P → ℕ
  | .base D => D.outputs
  | .descend _ _ copies _ _ _ _ next => copies * next.outputs
  | .partition _ _ _ _ children => ∏ j, (children j).outputs
  | .rotate D => D.outputs
  | .swap D => D.outputs

def RegionalPlan.dims {N ell : ℕ} {P : Predicate N} : RegionalPlan N ell P → ℕ × ℕ × ℕ
  | .base D => (D.a, D.b, D.c)
  | .descend _ _ _ _ _ _ _ next => next.dims
  | .partition _ _ _ _ children =>
      (∏ j, (children j).dims.1, ∏ j, (children j).dims.2.1, ∏ j, (children j).dims.2.2)
  | .rotate D => (D.dims.2.2, D.dims.1, D.dims.2.1)
  | .swap D => (D.dims.2.2, D.dims.2.1, D.dims.1)

def RegionalPlan.a {N ell : ℕ} {P : Predicate N} (D : RegionalPlan N ell P) : ℕ := D.dims.1
def RegionalPlan.b {N ell : ℕ} {P : Predicate N} (D : RegionalPlan N ell P) : ℕ := D.dims.2.1
def RegionalPlan.c {N ell : ℕ} {P : Predicate N} (D : RegionalPlan N ell P) : ℕ := D.dims.2.2

end MME.ProfiledCW


