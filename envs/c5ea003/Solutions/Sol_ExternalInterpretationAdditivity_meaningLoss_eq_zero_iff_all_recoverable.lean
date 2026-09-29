-- Prove2me | solution 1 for ExternalInterpretationAdditivity.meaningLoss_eq_zero_iff_all_recoverable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:09:12.925498+00:00
-- url     : https://prove2.me/submissions/1454d1ec-a9c7-4379-83cd-f28a07b08183

-- Sol generated from Applications/ExternalInterpretationAdditivity.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationAdditivity
import Definitions.Def_Applications_ExternalInterpretationDefinability
import Definitions.Def_Applications_ExternalInterpretationLogicalInvariance
import Theorems.Thm_ExternalInterpretationAdditivity_meaningLoss_eq_zero_iff_rigid
import Theorems.Thm_ExternalInterpretationDefinability_recoverable_iff_orbitConstant
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
theorem solution[Fintype M] [Fintype (orbitRel.Quotient G M)]
    {V : Type w} (x₀ y₀ : V) (hne : x₀ ≠ y₀) :
    meaningLoss G M = 0 ↔ ∀ I : M → V, Recoverable G I := by
  classical
  rw [meaningLoss_eq_zero_iff_rigid]
  constructor
  · intro h I
    rw [recoverable_iff_orbitConstant]
    intro x y hxy
    rw [h x y hxy]
  · intro h x y hxy
    by_contra hne'
    have hI := h (fun z => if z = x then x₀ else y₀)
    rw [recoverable_iff_orbitConstant] at hI
    have h2 : (if x = x then x₀ else y₀) = (if y = x then x₀ else y₀) := hI hxy
    rw [if_pos rfl, if_neg (Ne.symm hne')] at h2
    exact hne h2
