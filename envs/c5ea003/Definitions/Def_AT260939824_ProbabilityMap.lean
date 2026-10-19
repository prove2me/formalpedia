-- Prove2me | Definitions.Def_AT260939824_ProbabilityMap
-- name    : AT260939824_ProbabilityMap
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:48:00.748358+00:00
-- url     : https://prove2.me/theorems/d13cb3f2-9daa-4566-9db4-f95a7ddf64e8
-- title:
--   Pushforward on graph support-pair spaces
-- statement:
--   For a map $f:V\to W$ of finite vertex sets, pushing a probability distribution forward sums masses along the fibers of $f$. A graph homomorphism $H\to J$ sends a compatible pair of distributions on $H$ to a compatible pair on $J$. The resulting support-pair map is continuous and commutes with exchange of the two shores.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ProbabilityMap.lean, selected declaration lines 24-29, 31-32, 34-45, 47-60, 69-76, 78-80, 82-85, 87-88; SHA-256 cb014c832284cb745a6bb9bf6fe141347f0e037c4ed6a6b1e278783044ef77c1. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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
# Pushforward of probability support pairs

Graph homomorphisms induce continuous maps of the concrete support spaces,
commuting with the shore swaps. This permits removal of isolated vertices
without adding a neighbor-choice hypothesis to the target statements.
-/

open scoped BigOperators

namespace AbelianTargets

noncomputable section

namespace Probability

variable {V W : Type*} [Fintype V] [Fintype W]

attribute [local instance] Classical.propDecidable

def push (f : V → W) (p : Probability V) : Probability W := by
  classical
  exact {
    mass := fun w => ∑ v, if f v = w then p.mass v else 0
    nonneg := fun w => Finset.sum_nonneg (fun v _ => by split <;> simp [p.nonneg v])
    sum_one := by rw [Finset.sum_comm]; simpa using p.sum_one }

theorem push_mass (f : V → W) (p : Probability V) (w : W) :
    (push f p).mass w = ∑ v, if f v = w then p.mass v else 0 := rfl

theorem continuous_push (f : V → W) : Continuous (push f) := by
  classical
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro w
  change Continuous (fun p : Probability V => ∑ v, if f v = w then p.mass v else 0)
  apply continuous_finsetSum
  intro v _
  by_cases h : f v = w
  · simpa only [h, if_true] using continuous_mass_apply v
  · simp only [h, if_false]
    exact continuous_const

theorem push_pos_iff (f : V → W) (p : Probability V) (w : W) :
    0 < (push f p).mass w ↔ ∃ v, f v = w ∧ 0 < p.mass v := by
  classical
  rw [push_mass, Finset.sum_pos_iff_of_nonneg]
  · simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv⟩
      by_cases h : f v = w
      · exact ⟨v, h, by simpa only [h, if_true] using hv⟩
      · simp only [h, if_false, lt_self_iff_false] at hv
    · rintro ⟨v, hv, hp⟩
      exact ⟨v, by simpa only [hv, if_true] using hp⟩
  · intro v _
    split <;> simp [p.nonneg v]

end Probability

namespace SupportPair

variable {V W : Type*} [Fintype V] [Fintype W]
  {H : SimpleGraph V} {J : SimpleGraph W}

def map (f : H →g J) (z : SupportPair H) : SupportPair J :=
  ⟨(Probability.push f z.left, Probability.push f z.right), by
    intro a b ha hb
    obtain ⟨u, hu, hpu⟩ := (Probability.push_pos_iff f z.left a).mp ha
    obtain ⟨v, hv, hpv⟩ := (Probability.push_pos_iff f z.right b).mp hb
    subst a
    subst b
    exact f.map_adj (compatible H z u v hpu hpv)⟩

theorem continuous_map (f : H →g J) : Continuous (map f) :=
  (((Probability.continuous_push f).comp (continuous_left H)).prodMk
    ((Probability.continuous_push f).comp (continuous_right H))).subtype_mk _

@[simp] theorem map_swap (f : H →g J) (z : SupportPair H) :
    map f (swap H z) = swap J (map f z) := by
  apply Subtype.ext
  rfl

def continuousMap (f : H →g J) : ContinuousMap (SupportPair H) (SupportPair J) :=
  ⟨map f, continuous_map f⟩

end SupportPair

end

end AbelianTargets


