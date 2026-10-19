-- Prove2me | Definitions.Def_AT260939824_RectangularLocalFiniteness
-- name    : AT260939824_RectangularLocalFiniteness
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:44:36.544897+00:00
-- url     : https://prove2.me/theorems/8e3227c1-9cea-41ad-b774-1f74bf0adfd8
-- title:
--   Local finiteness from bounded integer side lengths
-- statement:
--   For integer rectangles in dimension $d$, the pair of endpoint vectors uniquely determines the rectangle. Hence finitely many rectangles have all endpoint coordinates in prescribed integer intervals. Given side bounds $K_i\in\mathbb N$, say $R$ has bounded sides if $u_i-\ell_i\le K_i$ for every $i$. For every $x\in\mathbb R^d$,
--   $$\{R:u_i-\ell_i\le K_i\ \forall i,\ R\cap B(x,1)\ne\varnothing\}$$
--   is finite, where the ball uses the maximum coordinate metric. An intersecting point bounds both endpoints between $x_i-1-K_i$ and $x_i+1+K_i$, reducing the assertion to finitely many integer endpoint choices.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RectangularLocalFiniteness.lean, selected declaration lines 21-27, 29-40, 42-43, 45-66; SHA-256 10f72217cf8a848d4f413def249f37b110fe58a896fb4deb5f480e6a0db820b3. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Local finiteness of bounded integer rectangles

Integer endpoints and a uniform coordinate diameter bound alone give a
locally finite family of distinct rectangles. Thus the same conclusion
applies both to retained full tiles and to their lower-dimensional strata.
-/

namespace AbelianTargets

noncomputable section

namespace RectangularCell

variable {d : ℕ}

theorem endpoint_pair_injective :
    Function.Injective (fun R : RectangularCell d => (R.lower,R.upper)) := by
  intro R S h
  cases R
  cases S
  cases h
  rfl

theorem finite_bounded_endpoints (a b : Fin d → ℤ) :
    {R : RectangularCell d | ∀ i,
      a i ≤ R.lower i ∧ R.lower i ≤ b i ∧ a i ≤ R.upper i ∧ R.upper i ≤ b i}.Finite := by
  have hfin : {u : Fin d → ℤ | ∀ i, u i ∈ Set.Icc (a i) (b i)}.Finite :=
    Set.Finite.pi' (fun i => Set.finite_Icc (a i) (b i))
  apply Set.Finite.of_injOn (f := fun R : RectangularCell d => (R.lower,R.upper))
    (t := {u : Fin d → ℤ | ∀ i, u i ∈ Set.Icc (a i) (b i)} ×ˢ
      {u : Fin d → ℤ | ∀ i, u i ∈ Set.Icc (a i) (b i)}) _ endpoint_pair_injective.injOn
    (hfin.prod hfin)
  intro R hR
  exact ⟨fun i => ⟨(hR i).1, (hR i).2.1⟩,
    fun i => ⟨(hR i).2.2.1, (hR i).2.2.2⟩⟩

def HasBoundedSides (K : Fin d → ℕ) (R : RectangularCell d) : Prop :=
  ∀ i, R.upper i-R.lower i ≤ (K i : ℤ)

theorem finite_meeting_ball (K : Fin d → ℕ) (x : RealCoordinates d) :
    {R : RectangularCell d | HasBoundedSides K R ∧
      (R.closedBox ∩ Metric.ball x 1).Nonempty}.Finite := by
  let a : Fin d → ℤ := fun i => Int.ceil (x i-1-(K i : ℝ))
  let b : Fin d → ℤ := fun i => Int.floor (x i+1+(K i : ℝ))
  apply (finite_bounded_endpoints a b).subset
  rintro R ⟨hR,y,hy,hyx⟩ i
  have hi : |y i-x i| ≤ 1 := by
    have hh : dist (y i) (x i) ≤ dist y x := dist_le_pi_dist y x i
    have hball : dist y x < 1 := hyx
    rw [Real.dist_eq] at hh
    exact hh.trans hball.le
  have hlohi := hy i
  have hord : (R.lower i : ℝ) ≤ (R.upper i : ℝ) := by exact_mod_cast R.ordered i
  have hdiam : (R.upper i : ℝ)-(R.lower i : ℝ) ≤ (K i : ℝ) := by
    exact_mod_cast hR i
  have hi' := abs_le.mp hi
  have hlower : x i-1-(K i : ℝ) ≤ (R.lower i : ℝ) := by linarith
  have hupper : (R.upper i : ℝ) ≤ x i+1+(K i : ℝ) := by linarith
  have ha : a i ≤ R.lower i := Int.ceil_le.mpr hlower
  have hb : R.upper i ≤ b i := Int.le_floor.mpr hupper
  exact ⟨ha,(R.ordered i).trans hb,ha.trans (R.ordered i),hb⟩







end RectangularCell

end

end AbelianTargets


