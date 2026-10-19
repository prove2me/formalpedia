-- Prove2me | Definitions.Def_AT260939824_Rounding
-- name    : AT260939824_Rounding
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:41:45.380117+00:00
-- url     : https://prove2.me/theorems/de4e807e-c5c1-44a9-a8e1-73c52fdaa3ac
-- title:
--   Finite-range probability fields for graph-homomorphism rounding
-- statement:
--   Let $\mathbb Z^d$ act on a topological space $X$, let $V$ be finite, and let $H$ be a simple graph on $V$. A probability field consists of maps $p,q:X\to\operatorname{Prob}(V)$ with $p$ continuous and of finite range, such that the positive supports of $p(x)$ and $q(x)$ are completely adjacent in $H$. It additionally requires
--   $$\left|p(e_i\cdot x)(v)-q(x)(v)\right|<\frac1{2|V|}
--   \qquad(x\in X,\ 1\le i\le d,\ v\in V).$$
--   Here $e_i$ is a positive unit lattice vector. No continuity or finite-range condition is imposed on $q$, and no freeness or continuity assumption is imposed on the action in this structure. This is the exact data rounded into a continuous finite-target graph homomorphism.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/Rounding.lean, selected declaration lines 27-40; SHA-256 c6f4d3914945f30a85748acd773b059f0eb10d8e43731909cc4911e70c910c0a. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Continuous finite-range rounding

The final step of Theorem 1.4 and Proposition 7.1 is proved here.
The existence of `ProbabilityField` is a separate, unproved geometric
obligation, never an axiom of this project.
-/

namespace AbelianTargets



/-- A finite-range probability field with the precise support and error
conditions constructed in Section 6 of the paper. Only the first shore
needs to be continuous for the rounding theorem. -/
structure ProbabilityField {d : ℕ} {X V : Type*}
    [AddAction (Lattice d) X] [TopologicalSpace X] [Fintype V]
    (H : SimpleGraph V) where
  p : X → Probability V
  q : X → Probability V
  continuous_p : Continuous p
  finite_range_p : (Set.range p).Finite
  compatible : ∀ x, Compatible H (p x) (q x)
  close : ∀ (x : X) (i : Fin d) (v : V),
    |(p (unitVector i +ᵥ x)).mass v - (q x).mass v| <
      1 / (2 * (Fintype.card V : ℝ))



end AbelianTargets


