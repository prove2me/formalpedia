-- Prove2me | Definitions.Def_AT260939824_Probability
-- name    : AT260939824_Probability
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:40:45.157895+00:00
-- url     : https://prove2.me/theorems/c659e974-1349-4b32-bc9f-d22b3f52f110
-- title:
--   Finite probability coordinates and compatible shores
-- statement:
--   For a finite vertex set $V$, a probability distribution is a nonnegative real mass function with total mass one:
--   $$\sum_{v\in V}p(v)=1.$$
--   It carries the topology induced by its mass coordinates, has a maximal-mass vertex, and forces $V$ to be nonempty. For a graph $H$, two distributions are compatible when every positive-mass vertex of one is adjacent to every positive-mass vertex of the other.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/Probability.lean, selected declaration lines 24-28, 34-36, 38-39, 41-43, 45-47, 49-50, 52-58, 60-77, 79-81, 104-107; SHA-256 27ae73f8cb16eda86f7b4dd30d130edf768099d7bd8322eb4ed130bf7497ebec. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Init
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false

/-!
# Probability coordinates and exact graph rounding

This file formalizes the numerical part of the proof of Theorem 1.4 in
arXiv:2609.39824, Section 6. It does not assume existence of the geometric
approximate parity field used earlier in that proof.
-/

open scoped BigOperators

namespace AbelianTargets

/-- A probability distribution on a finite vertex type. -/
@[ext] structure Probability (V : Type*) [Fintype V] where
  mass : V → ℝ
  nonneg : ∀ v, 0 ≤ mass v
  sum_one : ∑ v, mass v = 1

namespace Probability

variable {V : Type*} [Fintype V]

/-- Probability distributions carry the topology induced by their coordinates. -/
instance : TopologicalSpace (Probability V) :=
  TopologicalSpace.induced mass inferInstance

theorem continuous_mass : Continuous (mass : Probability V → V → ℝ) :=
  continuous_induced_dom

theorem continuous_mass_apply (v : V) :
    Continuous (fun p : Probability V => p.mass v) :=
  (continuous_apply v).comp continuous_mass

theorem mass_injective : Function.Injective (mass : Probability V → V → ℝ) := by
  intro p q h
  exact Probability.ext h

instance : T1Space (Probability V) :=
  t1Space_of_injective_of_continuous mass_injective continuous_mass

/-- An empty finite type cannot carry a probability distribution. -/
theorem nonempty (p : Probability V) : Nonempty V := by
  classical
  by_contra h
  haveI : IsEmpty V := not_nonempty_iff.mp h
  have hsum : (0 : ℝ) = 1 := by simpa using p.sum_one
  exact zero_ne_one hsum

/-- A finite probability distribution has a maximum of mass at least `1 / |V|`. -/
theorem exists_max_mass (p : Probability V) :
    ∃ v, (∀ w, p.mass w ≤ p.mass v) ∧
      1 / (Fintype.card V : ℝ) ≤ p.mass v := by
  classical
  letI : Nonempty V := p.nonempty
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ p.mass
    Finset.univ_nonempty
  have hmax : ∀ w, p.mass w ≤ p.mass v := fun w => hv w (Finset.mem_univ w)
  have hcard : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty V)
  have hsum : (1 : ℝ) ≤ (Fintype.card V : ℝ) * p.mass v := by
    calc
      1 = ∑ w, p.mass w := p.sum_one.symm
      _ ≤ ∑ _w : V, p.mass v := Finset.sum_le_sum (fun w _ => hmax w)
      _ = (Fintype.card V : ℝ) * p.mass v := by simp
  refine ⟨v, hmax, (div_le_iff₀ hcard).2 ?_⟩
  simpa only [mul_comm] using hsum

/-- A deterministic choice of a vertex with maximum probability mass. -/
noncomputable def chooseMax [Nonempty V] (p : Probability V) : V :=
  Classical.choose p.exists_max_mass









end Probability

variable {V : Type*} [Fintype V]

/-- Every positive-mass vertex in one shore is adjacent to every positive-mass
vertex in the other shore; this is the support condition defining `𝒟(H)`. -/
def Compatible (H : SimpleGraph V) (p q : Probability V) : Prop :=
  ∀ u v, 0 < p.mass u → 0 < q.mass v → H.Adj u v



end AbelianTargets


