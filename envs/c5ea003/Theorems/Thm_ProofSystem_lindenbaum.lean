-- Prove2me | Theorems.Thm_ProofSystem_lindenbaum
-- name    : ProofSystem.lindenbaum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:26:23.170989+00:00
-- url     : https://prove2.me/theorems/dbd6d8b8-6b08-4355-a716-2c18b4215c9e
-- title:
--   Lindenbaum's theorem.
-- statement:
--   **Lindenbaum's theorem.**  Every consistent theory extends to a *maximal*
--   consistent theory, which is automatically deductively closed.  Any intelligence
--   whose reasoning is compact can, in principle, complete its consistent
--   commitments to a maximal coherent worldview.
--
--   ```lean
--   theorem ProofSystem.lindenbaum{base : Set S} (hcon : P.Consistent base) :
--       ∃ M, base ⊆ M ∧ P.Consistent M ∧ P.C M = M ∧
--         ∀ Δ, M ⊆ Δ → P.Consistent Δ → Δ = M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalMathematicsLindenbaum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalMathematicsLindenbaum.lean#L88

-- Thm stub generated from Novelty/UniversalMathematicsLindenbaum.lean
import Mathlib
import Definitions.Def_Novelty_UniversalMathematicsLindenbaum

/-!
# Maximal consistent extensions and the finite character of consistency

This file deepens the study of *universal mathematics* — the theorems shared by
every consistent theory extending a base — by adding the one structural
ingredient that makes the theory of consistent extensions genuinely rich:
**compactness**.  A consequence operator is compact when every entailment
already follows from a *finite* portion of the assumptions.  This is the abstract
shadow of the fact that proofs are finite objects.

With compactness in hand we prove two results that a syntax-free intelligence
would need in order to reason about the space of consistent extensions of its
mathematics:

* `lindenbaum` — **every consistent theory extends to a maximal consistent
  one**, which is moreover deductively closed.  The proof is an order-theoretic
  Zorn's-lemma argument: the union of a chain of consistent theories is again
  consistent precisely *because* consistency has finite character.  This is the
  bridge between the lattice theory of theories and the logic of provability.

* `consistent_iff_finite` — **consistency has finite character**: a theory is
  consistent if and only if each of its finite sub-theories is.  This is the
  exact sense in which consistency, and hence membership in the universal core,
  can be certified by finite means.

An explicit compact model (`idProofSystem`) witnesses that the axioms — including
compactness — are jointly satisfiable, so none of the results are vacuous.
-/

open Set


open ProofSystem

variable {S : Type*} (P : ProofSystem S)

theorem ProofSystem.lindenbaum{base : Set S} (hcon : P.Consistent base) :
    ∃ M, base ⊆ M ∧ P.Consistent M ∧ P.C M = M ∧
      ∀ Δ, M ⊆ Δ → P.Consistent Δ → Δ = M := by sorry
