-- Prove2me | Theorems.Thm_normalized_eigencharacter_zero
-- name    : normalized_eigencharacter_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:27.436428+00:00
-- url     : https://prove2.me/theorems/317d2587-0321-4b8f-8e7a-6cd1dcc2e02f
-- title:
--   Normalized eigencharacter zero
-- statement:
--   Formal statement of `normalized_eigencharacter_zero` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem normalized_eigencharacter_zero{n : ℕ} (action : Fin n → MinPlusExpr n) (base : Fin n)
--       (v : Fin n → ℝ) (_hnorm : v base = 0) (eigval : ℝ)
--       (heig : isTropicalEigencharacter action v eigval)
--       (hbase : (action base).eval v = v base) : eigval = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalHecke/MinPlusAlgebra.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalHecke/MinPlusAlgebra.lean#L115

-- Thm stub generated from Bridges/TropicalHecke/MinPlusAlgebra.lean
import Mathlib
import Definitions.Def_Bridges_TropicalHecke_MinPlusAlgebra
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Min-plus (tropical) expression algebra

This file provides the min-plus expression algebra that underlies the
`Bridges.Skeleton` development of the tropical Satake skeleton.

An element of `MinPlusExpr n` is a formal expression in `n` variables built from
variables, tropical addition (`min`) and tropical multiplication (ordinary `+`),
i.e. the **min-plus** semiring.  Its evaluation `eval` at a real vector realises
the tropical semantics, and `eval_concave` records that every min-plus expression
is a concave function of the evaluation point (min is concave, `+` is affine).

`TropRelation` packages an equation `lhs = rhs` between two expressions; a real
vector *satisfies* the relation when both sides evaluate equally.  The
`(normalized) tropRelationLocus` of a list of relations is the polyhedral set of
vectors satisfying them (with a chosen base coordinate normalized to `0`).

Finally we record the Hecke-operator dynamics `heckeMap`, its fixed points, and
tropical eigencharacters, together with the basic lemmas relating eigenvalue `0`
to fixed points.
-/

noncomputable section


open MinPlusExpr





/-
Every min-plus expression is concave in the evaluation point.
-/

theorem normalized_eigencharacter_zero{n : ℕ} (action : Fin n → MinPlusExpr n) (base : Fin n)
    (v : Fin n → ℝ) (_hnorm : v base = 0) (eigval : ℝ)
    (heig : isTropicalEigencharacter action v eigval)
    (hbase : (action base).eval v = v base) : eigval = 0 := by sorry
