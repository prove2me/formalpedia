-- Prove2me | Theorems.Thm_ExternalInterpretationAdditivity_meaningLoss_eq_zero_iff_all_recoverable
-- name    : ExternalInterpretationAdditivity.meaningLoss_eq_zero_iff_all_recoverable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:50:43.879476+00:00
-- url     : https://prove2.me/theorems/12a0b3e7-b5fc-4e76-ba40-4628cc8de05b
-- title:
--   Equivalently: nothing is lost precisely when *every* external interpretation
-- statement:
--   Equivalently: nothing is lost precisely when *every* external interpretation
--   is recoverable from structural truth.
--
--   ```lean
--   theorem ExternalInterpretationAdditivity.meaningLoss_eq_zero_iff_all_recoverable[Fintype M] [Fintype (orbitRel.Quotient G M)]
--       {V : Type w} (x₀ y₀ : V) (hne : x₀ ≠ y₀) :
--       meaningLoss G M = 0 ↔ ∀ I : M → V, Recoverable G I := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ExternalInterpretationAdditivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ExternalInterpretationAdditivity.lean#L126

-- Thm stub generated from Applications/ExternalInterpretationAdditivity.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationAdditivity
import Definitions.Def_Applications_ExternalInterpretationDefinability
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

theorem ExternalInterpretationAdditivity.meaningLoss_eq_zero_iff_all_recoverable[Fintype M] [Fintype (orbitRel.Quotient G M)]
    {V : Type w} (x₀ y₀ : V) (hne : x₀ ≠ y₀) :
    meaningLoss G M = 0 ↔ ∀ I : M → V, Recoverable G I := by sorry
