-- Prove2me | Theorems.Thm_ExternalInterpretationAdditivity_meaningLoss_eq_sum_orbits
-- name    : ExternalInterpretationAdditivity.meaningLoss_eq_sum_orbits
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:39.458508+00:00
-- url     : https://prove2.me/theorems/ab99197a-2e82-45f4-bf03-8bf25609fe3e
-- title:
--   Orbit decomposition of the exponent.
-- statement:
--   **Orbit decomposition of the exponent.**  Meaning loss counts the duplicate
--   elements inside orbits: `ℓ(M) = Σ_{orbits O} (|O| − 1)`.
--
--   ```lean
--   theorem ExternalInterpretationAdditivity.meaningLoss_eq_sum_orbits[Fintype M] [Fintype (orbitRel.Quotient G M)]
--       [∀ ω : orbitRel.Quotient G M, Fintype (orbit G (Quotient.out ω))] :
--       meaningLoss G M
--         = ∑ ω : orbitRel.Quotient G M, (Fintype.card (orbit G (Quotient.out ω)) - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ExternalInterpretationAdditivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ExternalInterpretationAdditivity.lean#L146

-- Thm stub generated from Applications/ExternalInterpretationAdditivity.lean
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

theorem ExternalInterpretationAdditivity.meaningLoss_eq_sum_orbits[Fintype M] [Fintype (orbitRel.Quotient G M)]
    [∀ ω : orbitRel.Quotient G M, Fintype (orbit G (Quotient.out ω))] :
    meaningLoss G M
      = ∑ ω : orbitRel.Quotient G M, (Fintype.card (orbit G (Quotient.out ω)) - 1) := by sorry
