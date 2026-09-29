-- Prove2me | solution 1 for ExternalInterpretationAdditivity.meaningLoss_eq_sum_orbits
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:02:18.900696+00:00
-- url     : https://prove2.me/submissions/9b81cd75-3cd0-4647-b3f4-635b01ca3103

-- Sol generated from Applications/ExternalInterpretationAdditivity.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationAdditivity
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


open ExternalInterpretationAdditivity

open MulAction ExternalInterpretationDefinability ExternalInterpretationLogicalInvariance

universe u v w

variable {G : Type u} [Group G] {M N : Type v} [MulAction G M] [MulAction G N]

/-! ## Orbit spaces of disjoint unions -/



/-! ## The meaning-loss exponent -/







open ExternalInterpretationAdditivity in
theorem solution[Fintype M] [Fintype (orbitRel.Quotient G M)]
    [∀ ω : orbitRel.Quotient G M, Fintype (orbit G (Quotient.out ω))] :
    meaningLoss G M
      = ∑ ω : orbitRel.Quotient G M, (Fintype.card (orbit G (Quotient.out ω)) - 1) := by
  classical
  have hcard : Fintype.card M
      = ∑ ω : orbitRel.Quotient G M, Fintype.card (orbit G (Quotient.out ω)) := by
    rw [Fintype.card_congr (MulAction.selfEquivSigmaOrbits G M), Fintype.card_sigma]
  have hpos : ∀ ω : orbitRel.Quotient G M, 1 ≤ Fintype.card (orbit G (Quotient.out ω)) := by
    intro ω
    exact Fintype.card_pos_iff.mpr ⟨⟨_, MulAction.mem_orbit_self _⟩⟩
  have hsub : ∀ (s : Finset (orbitRel.Quotient G M)),
      ∑ ω ∈ s, (Fintype.card (orbit G (Quotient.out ω)) - 1)
        = (∑ ω ∈ s, Fintype.card (orbit G (Quotient.out ω))) - s.card := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have h1 : 1 ≤ Fintype.card (orbit G (Quotient.out a)) := hpos a
      have h3 : s.card ≤ ∑ ω ∈ s, Fintype.card (orbit G (Quotient.out ω)) := by
        calc s.card = ∑ _ω ∈ s, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum fun ω _ => hpos ω
      rw [ih]
      omega
  unfold meaningLoss
  rw [hsub Finset.univ, ← hcard, Finset.card_univ]
