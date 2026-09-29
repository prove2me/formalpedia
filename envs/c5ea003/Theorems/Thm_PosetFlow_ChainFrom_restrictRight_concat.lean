-- Prove2me | Theorems.Thm_PosetFlow_ChainFrom_restrictRight_concat
-- name    : PosetFlow.ChainFrom.restrictRight_concat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T14:03:09.429631+00:00
-- url     : https://prove2.me/theorems/91f6062c-73bd-42c5-85c7-13d556018d2e
-- title:
--   RestrictRight concat
-- statement:
--   Formal statement of `PosetFlow.ChainFrom.restrictRight_concat` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PosetFlow.ChainFrom.restrictRight_concat(C : ChainFrom x y) (D : ChainFrom y z) :
--       restrictRight (concat C D) (mem_concat_middle C D) = D := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PosetFlow/ChainPoset.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PosetFlow/ChainPoset.lean#L252

-- Thm stub generated from Algebra/PosetFlow/ChainPoset.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_OrderComplexEuler
import Theorems.Thm_PosetFlow_ChainFrom_mem_concat_middle

/-!
# The refinement poset of strictly increasing chains of a poset

This file formalises the combinatorial core of the *chain replacement of a poset
flow*.  For a poset `P` and `x y : P`, the paper considers the poset of strictly
increasing chains from `x` to `y`, ordered by refinement, and takes its simplicial
nerve as the space of execution paths from `x` to `y` of the replacement flow.

Here a chain from `x` to `y` is recorded by its underlying finite set
(`PosetFlow.ChainFrom x y`): a finite, totally ordered subset of `P` containing `x`
and `y` and contained in the interval `[x, y]`.  Refinement is inclusion of
carriers.  We prove:

* `PosetFlow.ChainFrom.bot_le` : the chain `{x, y}` is the least element, so the
  refinement poset is a cone.  This is why the chain replacement of a poset flow is
  a *replacement*: its path spaces are contractible.
* `PosetFlow.alternatingSum_chainFrom_eq_zero` : the Euler-characteristic shadow of
  that contractibility, obtained from `OrderComplexEuler`.
* `PosetFlow.ChainFrom.concat` and `PosetFlow.ChainFrom.concat_assoc` : the
  composition law of the chain replacement (a poset-enriched semicategory
  structure), which is monotone in each variable.
* `PosetFlow.chainSplitOrderIso` : the *unique factorisation* of a chain through an
  intermediate point, as an order isomorphism
  `{E : ChainFrom x z // y ∈ E} ≃o ChainFrom x y × ChainFrom y z`.  This is the
  combinatorial statement which, at the level of flows, says that concatenation
  identifies path spaces of composites.
-/

open PosetFlow

open Finset

variable {P : Type*} [PartialOrder P] [DecidableEq P] [DecidableLE P]


open ChainFrom

variable {x y z w : P}

theorem PosetFlow.ChainFrom.restrictRight_concat(C : ChainFrom x y) (D : ChainFrom y z) :
    restrictRight (concat C D) (mem_concat_middle C D) = D := by sorry
