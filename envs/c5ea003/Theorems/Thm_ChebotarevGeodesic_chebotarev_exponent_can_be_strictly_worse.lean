-- Prove2me | Theorems.Thm_ChebotarevGeodesic_chebotarev_exponent_can_be_strictly_worse
-- name    : ChebotarevGeodesic.chebotarev_exponent_can_be_strictly_worse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:20:32.51566+00:00
-- url     : https://prove2.me/theorems/82a8c83c-04e9-473b-bf6c-0b50a803743d
-- title:
--   C1, strictness.
-- statement:
--   **C1, strictness.**  Let `G` be a finite group with at least two conjugacy classes and let
--   `li` be any main term.  Then there are class counting functions `piC` such that
--
--   their sum is *exactly* `li`, so the prime geodesic theorem (the pushforward to the trivial
--     quotient) holds with every exponent whatsoever, while
--   for every class `C` the estimate `piC C = classDensity C Â· li + O(x^{Î¸+Îµ})` **fails** for
--     every `Î¸ < Î²`.
--
--   So the inequality `jointOptimalExponent (pushforward) â¤ jointOptimalExponent (family)` of
--   `jointOptimalExponent_pushforward_le` can be arbitrarily strict: the exponent of the prime
--   geodesic theorem carries no information at all about the Chebotarev exponents.
--
--   ```lean
--   theorem ChebotarevGeodesic.chebotarev_exponent_can_be_strictly_worse(G : Type*) [Group G] [Fintype G]
--       [DecidableEq G] [Fintype (ConjClasses G)]
--       (hcard : 2 ≤ Fintype.card (ConjClasses G)) (li : ℝ → ℝ) {θ β : ℝ} (hθβ : θ < β) :
--       ∃ piC : ConjClasses G → ℝ → ℝ,
--         (∀ x, ∑ C : ConjClasses G, piC C x = li x) ∧
--         (∀ θ' : ℝ, HasErrorExponent (fun x => ∑ C : ConjClasses G, piC C x) li θ') ∧
--         (∀ C, ¬ HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicQuotientExponent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicQuotientExponent.lean#L75

-- Thm stub generated from Shared/ChebotarevGeodesicQuotientExponent.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTransfer
/-
# Exponents under quotients: the pushforward can only improve them

Continuation of `Shared.ChebotarevGeodesicQuotient` (which proves `chebotarev_pushforward`:
the Chebotarev estimate descends to every quotient with the *same* exponent) and
`Shared.ChebotarevGeodesicTransfer` (which introduces `jointExponentSet` and
`jointOptimalExponent`).  This file addresses conjecture C1 of `FUTURE_DIRECTIONS.md`.

* `jointExponentSet_subset_pushforward` : every exponent admissible for the family of class
  counting functions of `G` is admissible for the pushed-forward family of a quotient `H`;
* `jointOptimalExponent_pushforward_le` : hence the joint optimal exponent can only *drop*
  along a surjection `G ↠ H`;
* `chebotarev_exponent_can_be_strictly_worse` : and the drop can be strict, in the extreme
  possible way.  For any finite group with at least two conjugacy classes there are class
  counting functions whose *total* is exactly the main term `li` — so the pushforward to the
  trivial quotient (that is, the prime geodesic theorem) holds with **every** exponent —
  while no single class satisfies **any** exponent below `β`.  The mechanism is cancellation
  inside a fibre: the deviations `w C · x^β` sum to zero.

Consequently the inequality of `jointOptimalExponent_pushforward_le` is genuinely one-sided:
knowing the prime geodesic theorem with a good exponent says nothing about the individual
Chebotarev estimates, whereas the converse implication is the content of
`chebotarev_pushforward`.
-/


open Finset Filter Function
open scoped Topology

open ChebotarevGeodesic


variable {G H : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Group H] [Fintype H] [DecidableEq H]
  [Fintype (ConjClasses G)] [Fintype (ConjClasses H)]




/-! ## Strictness: total cancellation inside a fibre -/

theorem ChebotarevGeodesic.chebotarev_exponent_can_be_strictly_worse(G : Type*) [Group G] [Fintype G]
    [DecidableEq G] [Fintype (ConjClasses G)]
    (hcard : 2 ≤ Fintype.card (ConjClasses G)) (li : ℝ → ℝ) {θ β : ℝ} (hθβ : θ < β) :
    ∃ piC : ConjClasses G → ℝ → ℝ,
      (∀ x, ∑ C : ConjClasses G, piC C x = li x) ∧
      (∀ θ' : ℝ, HasErrorExponent (fun x => ∑ C : ConjClasses G, piC C x) li θ') ∧
      (∀ C, ¬ HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ) := by sorry
