-- Prove2me | Definitions.Def_Applications_ExternalInterpretationAdditivity
-- name    : Applications_ExternalInterpretationAdditivity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:35.186177+00:00
-- url     : https://prove2.me/theorems/42f962d7-cf18-415a-b018-70998e823145
-- title:
--   Aether Catalog definitions — Applications_ExternalInterpretationAdditivity
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ExternalInterpretationAdditivity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ExternalInterpretationAdditivity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationLogicalInvariance
/-
# The Definability Boundary, IV: The Meaning-Loss Exponent

Continuation of `Catalog/Applications/ExternalInterpretationDefinability.lean`,
`…Graphs.lean` and `…LogicalInvariance.lean`.

`card_interpretations_split` isolated the exponent

  `ℓ(M) = |M| − #orbits`

as the exact amount of external meaning that structural truth destroys: the
recoverable interpretations form a `|V|^{ℓ(M)}`-fold smaller family than all
interpretations.  This file develops `ℓ` as a structural invariant.

* `sumQuotEquiv` : the orbit space of a disjoint union of two models is the
  disjoint union of their orbit spaces, hence `card_orbits_sum`.
* `meaningLoss_sum` : **additivity**, `ℓ(M ⊕ N) = ℓ(M) + ℓ(N)`.
* `meaningLoss_eq_zero_iff_rigid` : `ℓ(M) = 0` exactly for rigid models, those in
  which structurally indistinguishable elements are equal; equivalently, every
  external interpretation is recoverable
  (`meaningLoss_eq_zero_iff_all_recoverable`).
* `meaningLoss_eq_sum_orbits` : `ℓ(M) = Σ_{orbits O} (|O| − 1)`, so the exponent
  counts exactly the "duplicate" elements inside orbits.
-/


namespace ExternalInterpretationAdditivity

open MulAction ExternalInterpretationDefinability ExternalInterpretationLogicalInvariance

universe u v w

variable {G : Type u} [Group G] {M N : Type v} [MulAction G M] [MulAction G N]

/-! ## Orbit spaces of disjoint unions -/

/-- The orbit space of a disjoint union of two `G`-models is the disjoint union of
the two orbit spaces. -/
def sumQuotEquiv (G : Type u) [Group G] (M N : Type v) [MulAction G M] [MulAction G N] :
    orbitRel.Quotient G (M ⊕ N) ≃ orbitRel.Quotient G M ⊕ orbitRel.Quotient G N where
  toFun := Quotient.lift
    (fun x => Sum.elim (fun a => Sum.inl (Quotient.mk (orbitRel G M) a))
      (fun b => Sum.inr (Quotient.mk (orbitRel G N) b)) x) (by
      intro a b hab
      have hr : (orbitRel G (M ⊕ N)) a b := hab
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
      obtain ⟨g, hg⟩ := hr
      subst hg
      cases b with
      | inl b => exact congrArg Sum.inl (Quotient.sound ⟨g, rfl⟩)
      | inr b => exact congrArg Sum.inr (Quotient.sound ⟨g, rfl⟩))
  invFun := Sum.elim
    (Quotient.lift (fun a => Quotient.mk (orbitRel G (M ⊕ N)) (Sum.inl a)) (by
      intro a b hab
      have hr : (orbitRel G M) a b := hab
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
      obtain ⟨g, hg⟩ := hr
      exact Quotient.sound ⟨g, by rw [← hg]; rfl⟩))
    (Quotient.lift (fun b => Quotient.mk (orbitRel G (M ⊕ N)) (Sum.inr b)) (by
      intro a b hab
      have hr : (orbitRel G N) a b := hab
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
      obtain ⟨g, hg⟩ := hr
      exact Quotient.sound ⟨g, by rw [← hg]; rfl⟩))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => cases x <;> rfl
  right_inv := by
    rintro (q | q) <;> induction q using Quotient.inductionOn <;> rfl


/-! ## The meaning-loss exponent -/

/-- The **meaning-loss exponent** of a finite model: the number of elements minus
the number of automorphism orbits.  By `card_interpretations_split` the family of
recoverable interpretations is `|V|^{ℓ(M)}` times smaller than the family of all
interpretations. -/
def meaningLoss (G : Type u) (M : Type v) [Group G] [MulAction G M] [Fintype M]
    [Fintype (orbitRel.Quotient G M)] : ℕ :=
  Fintype.card M - Fintype.card (orbitRel.Quotient G M)





end ExternalInterpretationAdditivity


