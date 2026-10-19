-- Prove2me | Theorems.Thm_AbelianTargets_Probability_exists_commonPoint_close_of_face_bound
-- name    : AbelianTargets.Probability.exists_commonPoint_close_of_face_bound
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:47:44.608416+00:00
-- url     : https://prove2.me/theorems/df780914-86ff-48fb-acab-2c4f0090c3be
-- title:
--   Nearby bounded faces have a controlled common point
-- statement:
--   Let $V$ be finite and equip its probability simplex with the coordinate sup metric. Let $p,q$ be supported on finite subsets $s,t\subseteq V$, respectively, with $|s|,|t|\le N$ for a natural number $N$. If $N\,d(p,q)<1$, then there is a distribution $r$ supported on both $s$ and $t$ such that
--   $$d(p,r),\ d(q,r)\le(N+1)d(p,q).$$
--   The estimate depends on the sizes of the supporting faces rather than the total number of vertices.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Sections 3–6 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. This helper is formalization-specific infrastructure, not a separately numbered assertion of the paper. Original Lean proof: AbelianTargets/SimplexDimensionBounds.lean, lines 82–103; raw UTF-8 source SHA-256 3e1d1dbba2668368210a84a6d786429dbdad827b1a6315a2fa22b35046e8a8f7. No public source repository commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

/-!
# Common-face bounds depending on simplex dimension

The estimates depend on the number of vertices in a supporting simplex,
rather than on the total number of vertices of a growing interval carrier.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped BigOperators NNReal
namespace AbelianTargets.Probability
end AbelianTargets.Probability
open AbelianTargets
open AbelianTargets.Probability
variable {V : Type*} [Fintype V]

theorem AbelianTargets.Probability.exists_commonPoint_close_of_face_bound (p q : Probability V)
    (s t : Finset V) (hp : p.SupportedOn (s : Set V)) (hq : q.SupportedOn (t : Set V))
    (N : ℕ) (hs : s.card≤N) (ht : t.card≤N)
    (hclose : (N : ℝ)*dist p q < 1) :
    ∃ r : Probability V, r.SupportedOn (s : Set V) ∧ r.SupportedOn (t : Set V) ∧
      dist p r ≤ ((N : ℝ)+1)*dist p q ∧ dist q r ≤ ((N : ℝ)+1)*dist p q := by sorry
