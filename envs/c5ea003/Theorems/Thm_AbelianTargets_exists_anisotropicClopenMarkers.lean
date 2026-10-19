-- Prove2me | Theorems.Thm_AbelianTargets_exists_anisotropicClopenMarkers
-- name    : AbelianTargets.exists_anisotropicClopenMarkers
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:50:33.219572+00:00
-- url     : https://prove2.me/theorems/2623814e-525e-48e8-b9cc-0eb7b3379b70
-- title:
--   Free zero-dimensional actions admit anisotropic clopen markers
-- statement:
--   Let $d\in\mathbb N$, $L_1,\ldots,L_d\in\mathbb N$, and let $\mathbb Z^d$ act freely and continuously on a topological space $X$. Put $F_L=\{g\in\mathbb Z^d:g\ne0,\ |g_i|\le L_i\text{ for all }i\}$ and join $x$ to $y$ in $G_L$ when $g\cdot x=y$ for some $g\in F_L$. Assume $X$ is $T_1$, second countable, and has a clopen basis. There exists a clopen set $A\subseteq X$ such that, with $A_x=\{g\in\mathbb Z^d:g\cdot x\in A\}$, for every $x\in X$,
--   $$
--   u,v\in A_x,\ u\ne v\ \Longrightarrow\ \exists i,\ L_i<|u_i-v_i|,
--   $$
--   $$
--   \forall u\in\mathbb Z^d\ \exists v\in A_x\ \forall i,\ |u_i-v_i|\le L_i.
--   $$
--   The statement includes dimensions and scale coordinates equal to zero.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/AnisotropicMarkers.lean, lines 107–139; SHA256 3009ed642985035e32ca3a8b04afdbc1f45897ae80d2d903e683f0a3c5abc407.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Clopen markers at independent coordinate scales

The initial marker construction in Lemma 3.2 is proved for an actual free
continuous action. Each coordinate has its own scale. This is the input
to the later packing, priority, cut, and rectangular subdivision steps.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable [T1Space X] [SecondCountableTopology X]

theorem AbelianTargets.exists_anisotropicClopenMarkers (L : Fin d → ℕ)
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X)) :
    Nonempty (AnisotropicClopenMarkers d L X) := by sorry
