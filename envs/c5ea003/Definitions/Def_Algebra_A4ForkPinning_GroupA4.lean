-- Prove2me | Definitions.Def_Algebra_A4ForkPinning_GroupA4
-- name    : Algebra_A4ForkPinning_GroupA4
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:03:30.218495+00:00
-- url     : https://prove2.me/theorems/ee24b4b8-9a17-40c2-95df-28d4a7c8ab3e
-- title:
--   Aether Catalog definitions — Algebra_A4ForkPinning_GroupA4
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.A4ForkPinning.GroupA4`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/A4ForkPinning/GroupA4.lean by skeleton subtraction
import Mathlib
/-
# The group side of the A₄ fork: `V₄ = [A₄, A₄]` and the cubic character

The A₄-field of the experiment is the splitting field of `x⁴ + 8x + 12`
(square discriminant `576²`, no transpositions in the Frobenius statistics), so
its Galois group is `A₄`.  The fork under study is

`F₀(p) = [Frob p ∈ V₄]`,

and the claim of the experiment is that `F₀` is *congruence pinned* because it
factors through the abelianisation `A₄^ab = C₃`, while the finer fork
`F₁(p) = [Frob p = e]` cannot be pinned by any modulus because `e` and the three
double transpositions live in the same `V₄`-coset.

This file proves the group-theoretic content of those statements, entirely
inside `Equiv.Perm (Fin 4)`:

* `A4ForkPinning.V4` — the Klein subgroup, *defined intrinsically* as the set of
  even involutions (`σ² = 1`, `sign σ = 1`);
* `A4ForkPinning.commutator_alternating_eq_V4` — `⁅A₄, A₄⁆ = V₄`;
* `A4ForkPinning.commutator_alternatingGroup` — `[A₄,A₄] = V₄` inside `A₄`, and
* `A4ForkPinning.card_abelianization_alternating` — `|A₄^ab| = 3`:  the
  abelianisation is cyclic of order three, so the only characters available are
  **cubic** ones;
* `A4ForkPinning.chi` — the explicit cubic character `A₄ → ℤ/3` with
  `chi_mul`, `chi_eq_zero_iff` (`chi σ = 0 ↔ σ ∈ V₄`) and `chi_surjective`;
* `A4ForkPinning.root_signature` — the `[4,1,0]` root-count signature of `A₄`
  (in particular **no** Frobenius fixes exactly two roots), and
  `A4ForkPinning.mem_V4_iff_nroots` — `F₀ = [nroots ∈ {4,0}]`;
* `A4ForkPinning.card_*` — the Chebotarev rates `1/12, 2/3, 1/4, 1/3`;
* `A4ForkPinning.abelian_hom_eq_one_on_V4` — **within-`V₄` flatness**: *every*
  homomorphism from `A₄` to an abelian group is constant on `V₄`, so no abelian
  (i.e. congruence) datum can separate `e` from a double transposition.
-/
open scoped commutatorElement

namespace A4ForkPinning

open Equiv Equiv.Perm Finset

/-! ## The Klein four-group as the even involutions -/

set_option maxRecDepth 40000 in
/-- `V₄ ⊂ S₄`: the even involutions.  Concretely `{e, (01)(23), (02)(13), (03)(12)}`. -/
def V4 : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {σ | σ * σ = 1 ∧ Equiv.Perm.sign σ = 1}
  mul_mem' := by intro a b ha hb; revert ha hb; revert a b; decide
  one_mem' := by decide
  inv_mem' := by intro a ha; revert ha; revert a; decide

lemma mem_V4 {σ : Equiv.Perm (Fin 4)} : σ ∈ V4 ↔ σ * σ = 1 ∧ Equiv.Perm.sign σ = 1 := Iff.rfl

instance : DecidablePred (fun σ : Equiv.Perm (Fin 4) => σ ∈ V4) :=
  fun _ => decidable_of_iff _ mem_V4.symm

lemma V4_le_alternating : V4 ≤ alternatingGroup (Fin 4) := by
  intro σ hσ
  exact mem_alternatingGroup.2 (mem_V4.1 hσ).2

set_option maxRecDepth 100000 in
/-- `|V₄| = 4`. -/
theorem card_V4 : (univ.filter (fun σ : Equiv.Perm (Fin 4) => σ ∈ V4)).card = 4 := by decide


/-! ## `V₄` is the commutator subgroup of `A₄` -/

set_option maxRecDepth 400000 in
private lemma commutators_mem_V4 : ∀ a b : Equiv.Perm (Fin 4), Equiv.Perm.sign a = 1 →
    Equiv.Perm.sign b = 1 → ⁅a, b⁆ ∈ V4 := by decide

set_option maxRecDepth 400000 in
private lemma V4_is_commutators : ∀ v : Equiv.Perm (Fin 4), v ∈ V4 → ∃ a b : Equiv.Perm (Fin 4),
    Equiv.Perm.sign a = 1 ∧ Equiv.Perm.sign b = 1 ∧ ⁅a, b⁆ = v := by decide

/-- **`⁅A₄, A₄⁆ = V₄`.**  The commutator subgroup of the alternating group on four
letters is the Klein four-group. -/
theorem commutator_alternating_eq_V4 :
    ⁅alternatingGroup (Fin 4), alternatingGroup (Fin 4)⁆ = V4 := by
  refine le_antisymm (Subgroup.commutator_le.2 ?_) ?_
  · intro a ha b hb
    exact commutators_mem_V4 a b (mem_alternatingGroup.1 ha) (mem_alternatingGroup.1 hb)
  · intro v hv
    obtain ⟨a, b, ha, hb, hab⟩ := V4_is_commutators v hv
    rw [← hab]
    exact Subgroup.commutator_mem_commutator (mem_alternatingGroup.2 ha)
      (mem_alternatingGroup.2 hb)

/-- The same statement inside the group `A₄` itself: `[A₄, A₄] = V₄`. -/
theorem commutator_alternatingGroup :
    commutator (alternatingGroup (Fin 4)) = V4.subgroupOf (alternatingGroup (Fin 4)) := by
  have hinj : Function.Injective (alternatingGroup (Fin 4)).subtype := Subtype.coe_injective
  have h := Subgroup.map_subtype_commutator (alternatingGroup (Fin 4))
  rw [commutator_alternating_eq_V4] at h
  have := congrArg (Subgroup.comap (alternatingGroup (Fin 4)).subtype) h
  rwa [Subgroup.comap_map_eq_self_of_injective hinj] at this

/-! ## The abelianisation is cyclic of order three -/

theorem card_alternating_subtype : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

set_option maxRecDepth 100000 in
theorem card_V4_subgroupOf :
    Nat.card (V4.subgroupOf (alternatingGroup (Fin 4))) = 4 := by
  have h : Nat.card (V4.subgroupOf (alternatingGroup (Fin 4))) = Nat.card V4 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe V4_le_alternating).toEquiv
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa using card_V4

/-- **`|A₄^ab| = 3`.**  The abelianisation of `A₄` has order three: the *only*
characters of `A₄` are cubic.  (This is the structural reason a fork of `A₄` can
be pinned only by a cubic residue symbol.) -/
theorem card_abelianization_alternating :
    Nat.card (Abelianization (alternatingGroup (Fin 4))) = 3 := by
  have hcard := Subgroup.card_mul_index (commutator (alternatingGroup (Fin 4)))
  rw [commutator_alternatingGroup, card_V4_subgroupOf, card_alternating_subtype] at hcard
  have hindex : (V4.subgroupOf (alternatingGroup (Fin 4))).index = 3 := by omega
  calc Nat.card (Abelianization (alternatingGroup (Fin 4)))
      = (commutator (alternatingGroup (Fin 4))).index := rfl
    _ = 3 := by rw [commutator_alternatingGroup, hindex]

/-! ## The explicit cubic character of `A₄` -/

/-- A fixed `3`-cycle, used as a coset representative. -/
def c3 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 0 2

/-- The cubic character `chi : A₄ → ℤ/3`, reading off the `V₄`-coset of a
permutation.  (Outside `A₄` the value is meaningless.) -/
def chi (σ : Equiv.Perm (Fin 4)) : ZMod 3 :=
  if σ ∈ V4 then 0 else if σ * c3⁻¹ ∈ V4 then 1 else 2

set_option maxRecDepth 800000 in
/-- `chi` is a homomorphism on `A₄`: the promised character of `A₄^ab = C₃`. -/
theorem chi_mul : ∀ σ τ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 → Equiv.Perm.sign τ = 1 →
    chi (σ * τ) = chi σ + chi τ := by decide



/-! ## Root-count signature of `A₄` -/

/-- Number of roots of the quartic fixed by a Frobenius element, i.e. number of
degree-one factors of the reduction. -/
def nroots (σ : Equiv.Perm (Fin 4)) : ℕ := (univ.filter (fun i => σ i = i)).card




/-! ## Chebotarev rates -/




/-! ## Within-`V₄` flatness -/



end A4ForkPinning


