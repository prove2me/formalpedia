-- Prove2me | Definitions.Def_AT260939824_ParityFields
-- name    : AT260939824_ParityFields
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:43:03.716423+00:00
-- url     : https://prove2.me/theorems/9f90af7b-db35-4368-afcb-5204c75c4f64
-- title:
--   Projected anisotropic orbit-map data
-- statement:
--   Let $d\ge1$, let $X$ be a topological space with an action of $\mathbb Z^d$, let $Y$ be a metric space, and let $\tau:Y\to Y$ be a map. The real coordinate space is $\mathbb R^d$, with standard vectors $e_i$ and distinguished first axis $i_0$. Set $p_{i_0}=e_{i_0}$ and $p_i=e_{i_0}+e_i$ for $i\ne i_0$.
--
--   For $A\in\mathbb R$, $B:\mathbb N\to\mathbb R$, and natural scales $L,M$, the coordinate rates are
--   $$c_i=\begin{cases}A\log(L+2)/L&i=i_0,\\B(L)/M&i\ne i_0,\end{cases}$$
--   with total real division, $0^{-1}=0$. A projected anisotropic map records $F:X\times\mathbb R^d\to Y$ such that $x\mapsto F(x,0)$ is continuous with finite range and
--   $$F(e_i\cdot x,0)=\tau(F(x,p_i)),\qquad d_Y(F(x,u+s e_i),F(x,u))\le c_i|s|.$$
--   The coordinate estimate holds for every $x$, coordinate $i$, $u\in\mathbb R^d$, and real $s$. These are fields of the data record; their existence is a separate construction.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ParityFields.lean, selected declaration lines 17, 19-20, 22-24, 37-40, 42-54; SHA-256 c3b1893021c75adaa86213fe7e00c64aa3619fb3bd257063122e4e8a445f22eb. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# From controlled orbit maps to approximate parity fields

This checks the closing argument of Proposition 6.1. The geometric orbit
map is a visible input; the rectangular atlas and controlled carrier
extensions are not assumed as axioms or claimed to exist here.
-/

namespace AbelianTargets

noncomputable section

abbrev RealCoordinates (d : ℕ) := Fin d → ℝ

def realUnitVector {d : ℕ} (i : Fin d) : RealCoordinates d :=
  fun j => if j = i then 1 else 0

def parityStep {d : ℕ} (hd : 1 ≤ d) (i : Fin d) : RealCoordinates d :=
  if i = firstAxis hd then realUnitVector (firstAxis hd)
  else realUnitVector (firstAxis hd) + realUnitVector i



def anisotropicCoefficient {d : ℕ} (hd : 1 ≤ d)
    (A : ℝ) (B : ℕ → ℝ) (L M : ℕ) (i : Fin d) : ℝ :=
  if i = firstAxis hd then A * Real.log ((L : ℝ) + 2) / (L : ℝ)
  else B L / (M : ℝ)

/-- The actual projected orbit map data needed after Lemma 5.2.
All geometric and regularity obligations are explicit fields. -/
structure ProjectedAnisotropicMap
    {d : ℕ} {X Y : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
    [MetricSpace Y] (τ : Y → Y) (hd : 1 ≤ d)
    (A : ℝ) (B : ℕ → ℝ) (L M : ℕ) where
  orbitMap : X → RealCoordinates d → Y
  continuous_origin : Continuous (fun x => orbitMap x 0)
  finite_range_origin : (Set.range (fun x => orbitMap x 0)).Finite
  covariance : ∀ x i, orbitMap (unitVector i +ᵥ x) 0 = τ (orbitMap x (parityStep hd i))
  coordinate_bound : ∀ x i u s,
    dist (orbitMap x (u + s • realUnitVector i)) (orbitMap x u) ≤
      anisotropicCoefficient hd A B L M i * |s|







end

end AbelianTargets


