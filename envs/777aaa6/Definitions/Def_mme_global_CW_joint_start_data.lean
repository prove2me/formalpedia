-- Prove2me | Definitions.Def_mme_global_CW_joint_start_data
-- name    : mme_global_CW_joint_start_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-22T07:20:46.981167+00:00
-- url     : https://prove2.me/theorems/cad730ba-f243-4430-95f8-5ad297586a89
-- title:
--   Finite global CW extraction followed by a joint recipe
-- statement:
--   Finite global exact-type stages and their mode permutations, composed across disjoint parts into one whole-interface joint recipe. All hash incidence, hole, copy and profile-cover obligations are explicit finite data; no tensor restriction is assumed.
-- source:
--   More Asymmetry Proposition 5.1 / Theorem 5.3: finite global extraction interface.

import Definitions.Def_mme_global_CW_stage_data
import Definitions.Def_mme_logarithmic_joint_regional_CW_recipe
open BigOperators MME MME.ProfiledCW
set_option autoImplicit false
namespace MME.GlobalCW

/-- One global region, with the exact types covering its interface and a finite
integer copy budget computed from the actual hash incidence lower bound. -/
inductive Part : (M ell : ℕ) → Predicate M → Type
  | exact {M ell : ℕ} {T : Predicate M}
      (types : ℕ) (rate : ℝ) (rate_nonneg : 0 ≤ rate)
      (steps : Fin types → ExactStage ell M)
      (hash_budget : ∀ j, (steps j).hash.Budget)
      (copy_budget : ∀ j, ⌈Real.exp rate⌉₊ * 8 ^ (steps j).repairExponent ≤ ⌈(steps j).hash.lower⌉₊)
      (inside : ∀ j i x, (steps j).output i x → T i x)
      (cover : ∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i)) : Part M ell T
  | rotate {M ell T} (child : Part M ell T) : Part M ell (fun i ↦ T (cyclicPerm.symm i))
  | swap {M ell T} (child : Part M ell T) : Part M ell (fun i ↦ T (swapFirstTwoPerm.symm i))

def Part.inputs {M ell : ℕ} {T : Predicate M} : Part M ell T → ℕ
  | .exact types _ _ _ _ _ _ _ => types
  | .rotate D => D.inputs
  | .swap D => D.inputs

noncomputable def Part.rate {M ell : ℕ} {T : Predicate M} : Part M ell T → ℝ
  | .exact _ rate _ _ _ _ _ _ => rate
  | .rotate D => D.rate
  | .swap D => D.rate

/-- A genuine unpaired global extraction followed by a joint regional recipe on
its whole interface. Set parts = 6 for the six global orientations. No tensor map
is stored; all source, type-cover, and counting obligations are finite data. -/
structure Start (M ell : ℕ) where
  parts : ℕ
  size : Fin parts → ℕ
  positions : ((j : Fin parts) × Fin (size j)) ≃ Fin M
  T : ∀ j, Predicate (size j)
  steps : ∀ j, Part (size j) ell (T j)
  Q : Predicate M
  target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j,r⟩))
  next : RegionRealization.LogJointRecipe M ell Q

def Start.inputs {M ell : ℕ} (D : Start M ell) : ℕ :=
  (∏ j, (D.steps j).inputs) * D.next.inputs

noncomputable def Start.logOutputs {M ell : ℕ} (D : Start M ell) : ℝ :=
  (∑ j, (D.steps j).rate) + D.next.logOutputs

def Start.a {M ell : ℕ} (D : Start M ell) : ℕ := D.next.a
def Start.b {M ell : ℕ} (D : Start M ell) : ℕ := D.next.b
def Start.c {M ell : ℕ} (D : Start M ell) : ℕ := D.next.c

end MME.GlobalCW


