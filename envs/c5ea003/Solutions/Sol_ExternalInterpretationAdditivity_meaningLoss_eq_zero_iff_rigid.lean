-- Prove2me | solution 1 for ExternalInterpretationAdditivity.meaningLoss_eq_zero_iff_rigid
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:06:01.443636+00:00
-- url     : https://prove2.me/submissions/b3d08631-03b9-406f-8ddd-ed18d3ca7247

-- Sol generated from Applications/ExternalInterpretationAdditivity.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationAdditivity
import Definitions.Def_Applications_ExternalInterpretationDefinability
import Definitions.Def_Applications_ExternalInterpretationLogicalInvariance
import Theorems.Thm_ExternalInterpretationLogicalInvariance_card_orbits_le
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


open ExternalInterpretationAdditivity

open MulAction ExternalInterpretationDefinability ExternalInterpretationLogicalInvariance

universe u v w

variable {G : Type u} [Group G] {M N : Type v} [MulAction G M] [MulAction G N]

/-! ## Orbit spaces of disjoint unions -/



/-! ## The meaning-loss exponent -/







open ExternalInterpretationAdditivity in
theorem solution[Fintype M] [Fintype (orbitRel.Quotient G M)] :
    meaningLoss G M = 0 ↔ ∀ x y : M, Indist G x y → x = y := by
  have hsurj : Function.Surjective (Quotient.mk (orbitRel G M)) := Quotient.mk_surjective
  have hle : Fintype.card (orbitRel.Quotient G M) ≤ Fintype.card M := card_orbits_le
  constructor
  · intro h x y hxy
    have hcard : Fintype.card M = Fintype.card (orbitRel.Quotient G M) := by
      unfold meaningLoss at h; omega
    have hbij : Function.Bijective (Quotient.mk (orbitRel G M)) :=
      (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩
    exact hbij.1 (Quotient.sound (indist_iff_orbitRel.mp (indist_symm hxy)))
  · intro h
    have hinj : Function.Injective (Quotient.mk (orbitRel G M)) := by
      intro x y hxy
      have hr : (orbitRel G M) x y := Quotient.exact hxy
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
      obtain ⟨g, hg⟩ := hr
      exact (h y x ⟨g, hg⟩).symm
    have hcard : Fintype.card M ≤ Fintype.card (orbitRel.Quotient G M) :=
      Fintype.card_le_of_injective _ hinj
    unfold meaningLoss
    omega
