-- Prove2me | Theorems.Thm_A4ForkPinning_card_alternating
-- name    : A4ForkPinning.card_alternating
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:23:20.269317+00:00
-- url     : https://prove2.me/theorems/e989e8ae-3185-4ff9-95d7-4176b3e6a81c
-- title:
--   `|A₄| = 12`.
-- statement:
--   `|A₄| = 12`.
--
--   ```lean
--   theorem A4ForkPinning.card_alternating:
--       (univ.filter (fun σ : Equiv.Perm (Fin 4) => Equiv.Perm.sign σ = 1)).card = 12 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/A4ForkPinning/GroupA4.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/A4ForkPinning/GroupA4.lean#L65

-- Thm stub generated from Algebra/A4ForkPinning/GroupA4.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_GroupA4
/-
# The group side of the A₄ fork: `V₄ = [A₄, A₄]` and the cubic character

The A₄-field of the experiment is the splitting field of `x⁴ + 8x + 12`
(square discriminant `576²`, no transpositions in the Frobenius statistics), so
its Galois group is `A₄`.  The fork under study is

`F₀(p) = [Frob p ∈ V₄]`,

and the claim of the experiment is that `F₀` is *congruence pinned* because it
factors through the abelianisation `A₄^ab = C₃`, while the finer fork
`F₁(p) = [Frob p = e]` cannot be pinned by any modulus because `e` and the three
double transpositions live in the same `V₄`-coset.

This file proves the group-theoretic content of those statements, entirely
inside `Equiv.Perm (Fin 4)`:

* `A4ForkPinning.V4` — the Klein subgroup, *defined intrinsically* as the set of
  even involutions (`σ² = 1`, `sign σ = 1`);
* `A4ForkPinning.commutator_alternating_eq_V4` — `⁅A₄, A₄⁆ = V₄`;
* `A4ForkPinning.commutator_alternatingGroup` — `[A₄,A₄] = V₄` inside `A₄`, and
* `A4ForkPinning.card_abelianization_alternating` — `|A₄^ab| = 3`:  the
  abelianisation is cyclic of order three, so the only characters available are
  **cubic** ones;
* `A4ForkPinning.chi` — the explicit cubic character `A₄ → ℤ/3` with
  `chi_mul`, `chi_eq_zero_iff` (`chi σ = 0 ↔ σ ∈ V₄`) and `chi_surjective`;
* `A4ForkPinning.root_signature` — the `[4,1,0]` root-count signature of `A₄`
  (in particular **no** Frobenius fixes exactly two roots), and
  `A4ForkPinning.mem_V4_iff_nroots` — `F₀ = [nroots ∈ {4,0}]`;
* `A4ForkPinning.card_*` — the Chebotarev rates `1/12, 2/3, 1/4, 1/3`;
* `A4ForkPinning.abelian_hom_eq_one_on_V4` — **within-`V₄` flatness**: *every*
  homomorphism from `A₄` to an abelian group is constant on `V₄`, so no abelian
  (i.e. congruence) datum can separate `e` from a double transposition.
-/
open scoped commutatorElement

open A4ForkPinning

open Equiv Equiv.Perm Finset

/-! ## The Klein four-group as the even involutions -/






set_option maxRecDepth 100000 in

theorem A4ForkPinning.card_alternating:
    (univ.filter (fun σ : Equiv.Perm (Fin 4) => Equiv.Perm.sign σ = 1)).card = 12 := by sorry
