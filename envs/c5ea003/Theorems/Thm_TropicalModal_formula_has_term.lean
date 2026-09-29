-- Prove2me | Theorems.Thm_TropicalModal_formula_has_term
-- name    : TropicalModal.formula_has_term
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T10:43:14.548984+00:00
-- url     : https://prove2.me/theorems/f7a3d3ca-e14a-4003-a786-69a61ef495c7
-- title:
--   Formula has term
-- statement:
--   Formal statement of `TropicalModal.formula_has_term` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalModal.formula_has_term{α PropVar : Type} [Fintype α] [Nonempty α]
--       (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar) :
--       ∀ φ : ModalFormula PropVar,
--         ∃ t : TropicalTerm PropVar,
--           t.maxDepth ≤ ModalDepth φ ∧
--           ∀ z : α, evalModal F V φ z = evalTerm F V t z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalGodelKripkeReconstruction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalGodelKripkeReconstruction.lean#L211

-- Thm stub generated from Bridges/TropicalGodelKripkeReconstruction.lean
import Mathlib
import Definitions.Def_Bridges_TropicalGodelKripkeReconstruction
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Gödel–Kripke Reconstruction: Idempotent Modal Semantics

This file establishes a formally verified bridge between tropical (min-plus) algebra and
modal logic semantics. The central results are:

1. **Tropical Modal Semantics**: Modal formulas are interpreted over finite weighted
   transition systems using min-plus algebra, where diamond is tropical matrix-vector
   multiplication and conjunction is pointwise minimum.

2. **Diamond–Inf Distributivity**: The tropical diamond operator distributes over
   pointwise minimum (conjunction), establishing that modal propagation is a tropical
   linear map on the semimodule of valuations.

3. **Tropical Hennessy–Milner Theorem**: Two states are modally indistinguishable up to
   depth `d` if and only if they agree on all tropical transfer profiles — the iterated
   diamond applications to atomic valuations.

4. **Modal Reconstruction**: Under a spectral separation hypothesis, the depth-`d` modal
   theory determines a canonical weighted quotient frame, reconstructible from finitely
   many tropical transfer samples.

## Mathematical Context

In the min-plus semiring (ℝ, min, +):
- **Tropical addition** is `min(a, b)`
- **Tropical multiplication** is `a + b`
- **Diamond operator**: `(◇_A v)(x) = inf_y (A(x,y) + v(y))`

The key insight is that `a + min(b, c) = min(a+b, a+c)` (tropical distributivity)
implies that diamond distributes over conjunction, making the modal transfer operator
a tropical linear map. This connects modal logic to tropical linear algebra and
weighted automata theory.

## References

- Gaubert, Katz: "The Minkowski theorem for max-plus convex sets"
- Hennessy, Milner: "Algebraic laws for nondeterminism and concurrency"
- Litvinov, Maslov: "Idempotent mathematics and mathematical physics"
-/

noncomputable section

open Finset BigOperators

open TropicalModal

/-! ## §1. Core Structures -/




/-! ## §2. Modal Depth -/



/-! ## §3. Tropical Modal Evaluation -/



/-! ## §4. Key Algebraic Lemma: Inf-Min Distributivity -/

/-
**Finite inf distributes over min**: For finite nonempty types,
    `inf_y min(f y, g y) = min(inf_y f y, inf_y g y)`.
-/

/-! ## §5. Diamond–Inf Distributivity -/

/-
**Diamond distributes over conjunction**: `◇_A(min(v, w)) = min(◇_A(v), ◇_A(w))`
-/

/-! ## §6. Iterated Diamond -/




/-! ## §7. Tropical Normal Forms

Every positive modal formula is semantically equivalent to a pointwise minimum of
iterated diamond applications to atomic valuations. This structural decomposition
is the key to the Hennessy-Milner theorem. -/






/-
Evaluating a shifted term equals applying diamond to the original.
-/

/-
**Structural decomposition**: every positive modal formula has a tropical
    normal form — a min-tree of iterated diamond applications to atoms.
-/

theorem TropicalModal.formula_has_term{α PropVar : Type} [Fintype α] [Nonempty α]
    (F : TropicalKripkeFrame α) (V : TropicalValuation α PropVar) :
    ∀ φ : ModalFormula PropVar,
      ∃ t : TropicalTerm PropVar,
        t.maxDepth ≤ ModalDepth φ ∧
        ∀ z : α, evalModal F V φ z = evalTerm F V t z := by sorry
