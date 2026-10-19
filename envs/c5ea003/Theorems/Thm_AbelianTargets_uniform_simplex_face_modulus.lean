-- Prove2me | Theorems.Thm_AbelianTargets_uniform_simplex_face_modulus
-- name    : AbelianTargets.uniform_simplex_face_modulus
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:48:33.253507+00:00
-- url     : https://prove2.me/theorems/a6c99a2d-e374-4e24-8675-225de32f75c1
-- title:
--   Uniform continuity glues across bounded simplex faces
-- statement:
--   Let $I$ index finite vertex sets $V_i$, finite face families $\mathcal F_i$, and maps $f_i$ from their probability realizations into one pseudometric space $Z$. Suppose every face has at most $N$ vertices. If the restrictions of all $f_i$ to every individual face have one common modulus of continuity, then the maps on their entire realizations have one common modulus:
--   $$\forall\varepsilon>0\ \exists\delta>0\ \forall i,p,q,\quad d(p,q)<\delta\Longrightarrow d(f_i(p),f_i(q))<\varepsilon.$$
--   Distances on the realizations are induced by probability-coordinate sup distance.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Sections 3–6 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. This helper is formalization-specific infrastructure, not a separately numbered assertion of the paper. Original Lean proof: AbelianTargets/UniformSimplexGluing.lean, lines 14–55; raw UTF-8 source SHA-256 17fd896101fa9c0d74458f8f0b468865ea442ce2611d87424f71b5faafb39cf6. No public source repository commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplexMetricGluing
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
# A uniform modulus on families of bounded-dimensional simplex unions

The vertex sets and number of simplices may grow. A common simplex size bound
and a common modulus on individual faces suffice for a common global modulus.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets

theorem AbelianTargets.uniform_simplex_face_modulus {I : Type*} {V : I → Type*}
    [∀ i, Fintype (V i)] {Z : Type*} [PseudoMetricSpace Z]
    (F : ∀ i, Finset (Finset (V i))) (f : ∀ i, SimplicialCarrier (F i) → Z)
    (N : ℕ) (hN : ∀ i s, s ∈ F i → s.card ≤ N)
    (hface : ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧
      ∀ i s, s ∈ F i → ∀ p q : SimplicialCarrier (F i),
        p.1.SupportedOn (s : Set (V i)) → q.1.SupportedOn (s : Set (V i)) →
        dist p q < δ → dist (f i p) (f i q) < ε) :
    ∀ ε : ℝ, 0<ε → ∃ δ : ℝ, 0<δ ∧ ∀ i (p q : SimplicialCarrier (F i)),
      dist p q < δ → dist (f i p) (f i q) < ε := by sorry
