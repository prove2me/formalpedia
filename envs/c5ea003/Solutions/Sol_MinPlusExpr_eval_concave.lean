-- Prove2me | solution 1 for MinPlusExpr.eval_concave
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:08:33.232361+00:00
-- url     : https://prove2.me/submissions/f85e08e6-3867-4067-bbc6-4c861a48b817

-- Sol generated from Bridges/TropicalHecke/MinPlusAlgebra.lean
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














open MinPlusExpr in
theorem solution{n : ℕ} (e : MinPlusExpr n) (v w : Fin n → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    e.eval (fun j => (1 - t) * v j + t * w j) ≥ (1 - t) * e.eval v + t * e.eval w := by
  induction' e with i a b ih_a ih_b;
  · simp [MinPlusExpr.eval];
  · simp [MinPlusExpr.eval];
    constructor <;> nlinarith [ min_le_left ( a.eval v ) ( b.eval v ), min_le_right ( a.eval v ) ( b.eval v ), min_le_left ( a.eval w ) ( b.eval w ), min_le_right ( a.eval w ) ( b.eval w ) ];
  · simp_all +decide [ MinPlusExpr.eval ] ; linarith!
