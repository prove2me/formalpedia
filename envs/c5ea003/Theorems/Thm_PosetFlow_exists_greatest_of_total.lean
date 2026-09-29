-- Prove2me | Theorems.Thm_PosetFlow_exists_greatest_of_total
-- name    : PosetFlow.exists_greatest_of_total
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:49:24.948167+00:00
-- url     : https://prove2.me/theorems/dd265d62-0966-448e-8e4e-94e8e4697b7e
-- title:
--   A nonempty totally ordered finset of a poset has a greatest element.
-- statement:
--   A nonempty totally ordered finset of a poset has a greatest element.
--
--   ```lean
--   theorem PosetFlow.exists_greatest_of_total(S : Finset P) (hne : S.Nonempty)
--       (htot : ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) : ∃ z ∈ S, ∀ a ∈ S, a ≤ z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PosetFlow/HallMobius.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PosetFlow/HallMobius.lean#L95

-- Thm stub generated from Algebra/PosetFlow/HallMobius.lean
import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_HallMobius

/-!
# Philip Hall's theorem: chains of a poset compute its Möbius function

The chain replacement of a poset flow replaces the (one point) spaces of execution
paths of a poset flow by the nerves of the refinement posets of chains.  The Euler
characteristics of those nerves are governed by the classical theorem of Philip
Hall, which identifies the alternating sum over chains from `x` to `y` with the
Möbius function of the incidence algebra.

This file proves Hall's theorem in the form

`∑ C ∈ chainFinsets x y, (-1) ^ |C| = - μ x y`,

where `chainFinsets x y` is the finite set of carriers of chains from `x` to `y`
(the objects of the refinement poset `PosetFlow.ChainFrom x y` of
`Algebra.PosetFlow.ChainPoset`), and `μ` is `IncidenceAlgebra.mu`.

## Main results

* `PosetFlow.chainAltSum_recursion` : deleting the top element `y` of a chain
  identifies chains from `x` to `y` with pairs `(z, C)` where `z ∈ Ico x y` and `C`
  is a chain from `x` to `z`.  This is the combinatorial induction step.
* `PosetFlow.chainAltSum_eq_neg_mu` : **Philip Hall's theorem**.
* `PosetFlow.mu_eq_zero_of_not_le` : the Möbius function vanishes off the order,
  a corollary of the chain description.
-/

open PosetFlow

open Finset IncidenceAlgebra

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]









omit [Fintype P] [DecidableLE P] in

theorem PosetFlow.exists_greatest_of_total(S : Finset P) (hne : S.Nonempty)
    (htot : ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) : ∃ z ∈ S, ∀ a ∈ S, a ≤ z := by sorry
