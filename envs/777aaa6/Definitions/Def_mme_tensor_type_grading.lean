-- Prove2me | Definitions.Def_mme_tensor_type_grading
-- name    : mme_tensor_type_grading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-31T17:43:44.835497+00:00
-- url     : https://prove2.me/theorems/d356dcb6-a40d-4b63-9592-40d83c5c2220
-- statement:
--   **Mode-wise type-grading on tensor objects** — the abstract data input every laser-method-style argument needs.
--
--   For an order-`d` tensor object `T : TensorObj K d`, a `TypeGrading T t` is a `t`-way direct-sum decomposition of each of the `d` mode spaces:
--
--   $$\forall i \in \{0, \ldots, d{-}1\},\quad T.V_i \;=\; \bigoplus_{\alpha \in \mathrm{Fin}\,t} G_{i,\alpha}.$$
--
--   Equivalently, it is a choice of `Fin t`-many `Submodule K (T.V i)` for each mode `i`, together with a `DirectSum.IsInternal` proof that the family is an internal direct sum.
--
--   **Role in the laser method.** The grading lets one assign a "type" (an element of `Fin t`) to every basis index of every mode, and read off the *type-triple* of any rank-one term as an element of `(Fin t)^d`. The combinatorics of these type-triples — which triples appear, with what multiplicity, under what symmetry — is the entire object of study for the laser method.
--
--   **Examples.**
--
--   * **Coppersmith–Winograd tensor `T_q`**: canonical 3-grading partitioning each mode's basis $\{0, 1, \ldots, q, q{+}1\}$ into `{0}`, `{1, ..., q}`, `{q+1}`.
--   * **Matrix-multiplication tensor `MM(n,m,p)`**: trivial 1-grading (a single class per mode).
--   * **Stothers 2010 / VW 2012 / Le Gall 2014**: each works with the CW tensor's *symmetric tensor power* and a corresponding refined grading; the abstraction here covers all of them.
--
--   **Reusability.** Every present and future ω-bound paper instantiates this same structure with its own tensor and grading. The abstract laser theorem `mme_laser_value_lower_bound` is stated against this abstraction — paper-agnostic by design.
-- source:
--   https://arxiv.org/abs/2212.11824

import Mathlib.Algebra.DirectSum.Module
import Definitions.Def_mme_tensor

/-! # Mode-wise type-gradings on tensor objects

A `TypeGrading T t` is a `t`-way direct-sum decomposition of each of the `d`
mode spaces of `T : TensorObj K d`. This is the abstract data input that
every "laser-method"-style argument needs: it lets one assign a type
`Fin t` to each basis index (within each mode) and read off the
"type-triple" of any rank-one term as an element of `(Fin t)^d`.

The CW tensor `T_q : TensorObj K 3` has a canonical `3`-grading whose
classes on each mode are `{0}` (the "left boundary"), `{1, …, q}`
(the "middle"), and `{q+1}` (the "right boundary"). The matrix-
multiplication tensor `MM(n,m,p)` admits its own grading (trivial,
i.e. `t = 1`). Stothers 2010, Vassilevska Williams 2012, Le Gall 2014
each work with their own tensors and gradings; all of them ride this
same abstraction.

**This file deliberately contains no theorems** — only the structural
definitions and basic typeclass instances. The abstract laser theorem
and its consumers live in separate files. -/

universe u

open DirectSum

namespace MME

variable {K : Type u} [Field K] {d : ℕ}

/-- A `t`-way mode-wise direct-sum decomposition of a tensor object's mode
spaces. -/
structure TensorObj.TypeGrading (T : TensorObj K d) (t : ℕ) where
  /-- For each mode `i`, a family of `t` submodules of `T.V i`. -/
  decomp : ∀ i : Fin d, Fin t → Submodule K (T.V i)
  /-- For each mode, the family is an internal direct sum: every vector in
  `T.V i` decomposes uniquely as a sum of pieces from the `t` submodules. -/
  is_internal : ∀ i : Fin d, DirectSum.IsInternal (decomp i)

namespace TensorObj.TypeGrading

variable {T : TensorObj K d} {t : ℕ}

/-- The "type" of a basis index, when the grading actually has the index in
exactly one class.  Recorded as a `Submodule` rather than a class-index so
the API stays usable in cases where the grading's class assignment is by
quotient rather than literal indexing. -/
@[reducible] def classOf (G : T.TypeGrading t) (i : Fin d) (α : Fin t) :
    Submodule K (T.V i) := G.decomp i α

end TensorObj.TypeGrading

end MME


