-- Prove2me | Definitions.Def_AT260939824_AtlasPacking
-- name    : AT260939824_AtlasPacking
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:42:27.594714+00:00
-- url     : https://prove2.me/theorems/bf82864c-d4c7-47b9-a152-e185d501143a
-- title:
--   Packing indices for anisotropic marker neighborhoods
-- statement:
--   Let $S$ be a nonnegative integer, let positive integers $L_i$ be coordinate scales, and let distinct lattice points of a finite set $A$ differ by more than $L_i$ in at least one coordinate. If $|a_i|\le SL_i$ for every $a\in A$, then
--
--   $$ |A|\le(2S+1)^d. $$
--
--   The associated finite bucket index records the integer quotient of each coordinate. This gives the explicit neighborhood-size parameter used by marker priorities and separated cuts.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasPacking.lean, selected declaration lines 16-26, 28-32, 34-40, 42-69; SHA-256 a51a2218e1ec97f95a7f85e06d138676c49c442458c4e849a7ffc11b88181354. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Anisotropic marker packing

Integer quotient buckets prove the uniform finite bound for markers in
a scaled box. The bound is independent of the coordinate scales, as
required by the priority construction of the rectangular atlas.
-/

namespace AbelianTargets

theorem abs_sub_lt_of_ediv_eq {a b l : ℤ} (hl : 0 < l)
    (heq : a/l = b/l) : |a-b| < l := by
  have ha₀ := Int.emod_nonneg a hl.ne'
  have hb₀ := Int.emod_nonneg b hl.ne'
  have ha₁ := Int.emod_lt_of_pos a hl
  have hb₁ := Int.emod_lt_of_pos b hl
  have ha := Int.emod_add_ediv_mul a l
  have hb := Int.emod_add_ediv_mul b l
  rw [heq] at ha
  rw [abs_lt]
  omega

def packingBucket (S : ℕ) (x l : ℤ) (hl : 0 < l)
    (hx : -(S : ℤ)*l ≤ x ∧ x ≤ (S : ℤ)*l) : Fin (2*S+1) := by
  have hlo : -(S : ℤ) ≤ x/l := (Int.le_ediv_iff_mul_le hl).mpr hx.1
  have hhi : x/l ≤ (S : ℤ) := (Int.ediv_le_iff_le_mul hl).mpr (by omega)
  exact ⟨(x/l+S).toNat, by omega⟩

theorem packingBucket_value (S : ℕ) (x l : ℤ) (hl : 0 < l)
    (hx : -(S : ℤ)*l ≤ x ∧ x ≤ (S : ℤ)*l) :
    ((packingBucket S x l hl hx).val : ℤ) = x/l+S := by
  change ((x/l+S).toNat : ℤ) = x/l+S
  apply Int.toNat_of_nonneg
  have := (Int.le_ediv_iff_mul_le hl).mpr hx.1
  omega

/-- A separated marker family has at most `(2S+1)^d` points within
scaled coordinate distance `S` of a chosen origin. -/
theorem anisotropic_marker_packing {d : ℕ} (S : ℕ) (L : Fin d → ℕ)
    (hL : ∀ i, 1 ≤ L i) (A : Finset (Lattice d))
    (hbounded : ∀ a ∈ A, ∀ i, -(S : ℤ)*(L i : ℤ) ≤ a i ∧ a i ≤ (S : ℤ)*(L i : ℤ))
    (hseparated : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∃ i, (L i : ℤ) < |a i-b i|) :
    A.card ≤ (2*S+1)^d := by
  classical
  have hpos : ∀ i, 0 < (L i : ℤ) := by
    intro i
    exact_mod_cast (show 0 < L i by have := hL i; omega)
  let bucket : A → (Fin d → Fin (2*S+1)) :=
    fun a i => packingBucket S (a.val i) (L i) (hpos i) (hbounded a.val a.property i)
  have hinj : Function.Injective bucket := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    obtain ⟨i,hi⟩ := hseparated a.val a.property b.val b.property hne
    have hcoord := congrArg (fun f : Fin d → Fin (2*S+1) => ((f i).val : ℤ)) hab
    have heq : a.val i/(L i : ℤ) = b.val i/(L i : ℤ) := by
      change ((packingBucket S (a.val i) (L i) (hpos i) (hbounded a.val a.property i)).val : ℤ) =
        ((packingBucket S (b.val i) (L i) (hpos i) (hbounded b.val b.property i)).val : ℤ) at hcoord
      rw [packingBucket_value,packingBucket_value] at hcoord
      omega
    have := abs_sub_lt_of_ediv_eq (hpos i) heq
    omega
  have hc := Fintype.card_le_of_injective bucket hinj
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hc



end AbelianTargets


