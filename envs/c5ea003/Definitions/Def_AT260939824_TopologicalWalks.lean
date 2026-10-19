-- Prove2me | Definitions.Def_AT260939824_TopologicalWalks
-- name    : AT260939824_TopologicalWalks
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:20:49.06255+00:00
-- url     : https://prove2.me/theorems/c6398d54-5e4f-4fbc-af3d-e85c295d42a4
-- title:
--   Topological realization of graph walks and reduced edge classes
-- statement:
--   Let $H$ be a simple graph on $V$, $X$ a topological space, and $f:V\to X$ a vertex map. An edge realization assigns each oriented graph edge a path from $f(a)$ to $f(b)$; concatenation defines a path for every graph walk, with the empty walk constant. One may instead assign relative homotopy classes of paths and concatenate those classes. A reduced edge-class realization requires
--   $$E(b\to a)=E(a\to b)^{-1},\qquad [P]=1\ \text{for every closed four-edge walk }P.$$
--   These are precisely the reversal and four-walk conditions needed for the realization to respect the reduced graph-homotopy relation.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/TopologicalWalks.lean, selected declaration lines 19-20, 22, 24-27, 29-33, 35-36, 38-40, 79-84; SHA-256 f11a33ac93c5da61346d28cb19716408cc94c378af7d66c339e17520b930f6de. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_ReducedWalks
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

/-!
# Passing the reduced walk presentation to topological path classes

This file proves the presentation argument used in Lemma 6.2.  A realization
of graph edges in a space, respecting reversal and filling every four-walk,
factors through the reduced graph-walk homotopy relation.  The geometric
edge maps and fillings themselves are constructed in `SupportGeometry`.
-/

namespace AbelianTargets

noncomputable section

variable {V X : Type*} [TopologicalSpace X] (H : SimpleGraph V) (f : V → X)

/-- A choice of topological path class for each oriented graph edge. -/
abbrev EdgeClasses := ∀ ⦃a b : V⦄, H.Adj a b → Path.Homotopic.Quotient (f a) (f b)

abbrev EdgePaths := ∀ ⦃a b : V⦄, H.Adj a b → Path (f a) (f b)

/-- An actual continuous path, obtained by concatenating realized graph edges. -/
def walkPath (E : EdgePaths H f) : {a b : V} → H.Walk a b → Path (f a) (f b)
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (E h).trans (walkPath E p)

/-- Concatenate the edge classes along an actual graph walk. -/
def walkClass (E : EdgeClasses H f) : {a b : V} → H.Walk a b →
    Path.Homotopic.Quotient (f a) (f b)
  | _, _, .nil => Path.Homotopic.Quotient.refl _
  | _, _, .cons h p => Path.Homotopic.Quotient.trans (E h) (walkClass E p)

@[simp] theorem walkClass_nil (E : EdgeClasses H f) (a : V) :
    walkClass H f E (SimpleGraph.Walk.nil : H.Walk a a) = Path.Homotopic.Quotient.refl (f a) := rfl

@[simp] theorem walkClass_cons (E : EdgeClasses H f) {a b c : V}
    (h : H.Adj a b) (p : H.Walk b c) :
    walkClass H f E (.cons h p) = Path.Homotopic.Quotient.trans (E h) (walkClass H f E p) := rfl









/-- The exact hypotheses a topological edge realization must check. -/
structure ReducedEdgeClasses where
  edge : EdgeClasses H f
  reverse : ∀ ⦃a b⦄ (h : H.Adj a b), edge h.symm = Path.Homotopic.Quotient.symm (edge h)
  four : ∀ ⦃a⦄ (p : H.Walk a a), p.length = 4 →
    walkClass H f edge p = Path.Homotopic.Quotient.refl (f a)

namespace ReducedEdgeClasses

variable {H f}





end ReducedEdgeClasses

end

end AbelianTargets


