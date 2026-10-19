-- Prove2me | Definitions.Def_AT260939824_IntegerIntervalGluing
-- name    : AT260939824_IntegerIntervalGluing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:47:46.312171+00:00
-- url     : https://prove2.me/theorems/c027f597-f940-498c-85a2-eebed3c9e5e8
-- title:
--   Clamping and gluing on integer intervals
-- statement:
--   For integers $A\le B$, the clamp map sends a real parameter to the nearest point of the closed interval $[A,B]$ and fixes that interval. Let $f:\mathbb R\to Z$ take values in a pseudometric space. If $f$ has Lipschitz constant $K$ on every integer unit subinterval of $[A,B]$, then its composition with the clamp map is globally $K$-Lipschitz.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/IntegerIntervalGluing.lean, selected declaration lines 8, 10-14, 16-17, 19-22, 24-27, 29-56; SHA-256 4d9fc2435aa3dab978e6498b23fe09d3c3c354cf6275a65078d2b3be4ccbfd7c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_IntegerCellGluing
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
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-! Unit-interval gluing on an integer bounded coordinate interval. -/
namespace AbelianTargets
open scoped NNReal
noncomputable section

def integerIntervalClamp (A B : ℤ) (t : ℝ) : ℝ := max (A : ℝ) (min (B : ℝ) t)

theorem integerIntervalClamp_mem {A B : ℤ} (hAB : A≤B) (t : ℝ) :
    integerIntervalClamp A B t∈Set.Icc (A : ℝ) (B : ℝ) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by exact_mod_cast hAB) (min_le_left _ _)

theorem integerIntervalClamp_eq {A B : ℤ} {t : ℝ} (ht : t∈Set.Icc (A : ℝ) (B : ℝ)) :
    integerIntervalClamp A B t=t := by simp [integerIntervalClamp,min_eq_right ht.2,max_eq_right ht.1]

theorem integerIntervalClamp_low {A B : ℤ} (hAB : A≤B) {t : ℝ} (ht : t≤(A : ℝ)) :
    integerIntervalClamp A B t=(A : ℝ) := by
  have hAB' : (A : ℝ)≤B := by exact_mod_cast hAB
  simp [integerIntervalClamp,min_eq_right (ht.trans hAB'),max_eq_left ht]

theorem integerIntervalClamp_high {A B : ℤ} (hAB : A≤B) {t : ℝ} (ht : (B : ℝ)≤t) :
    integerIntervalClamp A B t=(B : ℝ) := by
  have hAB' : (A : ℝ)≤B := by exact_mod_cast hAB
  simp [integerIntervalClamp,min_eq_left ht,max_eq_right hAB']

theorem lipschitz_integer_clamped_intervals {Z : Type*} [PseudoMetricSpace Z]
    (A B : ℤ) (hAB : A≤B) (f : ℝ→Z) (K : ℝ≥0)
    (hunit : ∀ n : ℤ,A≤n→n+1≤B→∀ x∈Set.Icc (n : ℝ) ((n : ℝ)+1),
      ∀ y∈Set.Icc (n : ℝ) ((n : ℝ)+1),dist (f x) (f y)≤K*|x-y|) :
    LipschitzWith K (fun t => f (integerIntervalClamp A B t)) := by
  apply lipschitz_real_of_integer_intervals
  intro n x hx y hy
  by_cases hlo : n<A
  · have hn : n+1≤A := by omega
    have hn' : (n : ℝ)+1≤A := by exact_mod_cast hn
    rw [integerIntervalClamp_low hAB (hx.2.trans hn'),integerIntervalClamp_low hAB (hy.2.trans hn')]
    simp only [dist_self]
    exact mul_nonneg K.2 (abs_nonneg _)
  · by_cases hhi : B≤n
    · have hn' : (B : ℝ)≤n := by exact_mod_cast hhi
      rw [integerIntervalClamp_high hAB (hn'.trans hx.1),integerIntervalClamp_high hAB (hn'.trans hy.1)]
      simp only [dist_self]
      exact mul_nonneg K.2 (abs_nonneg _)
    · have hnA : A≤n := le_of_not_gt hlo
      have hnB : n+1≤B := by omega
      have hxR : x∈Set.Icc (A : ℝ) (B : ℝ) :=
        ⟨(show (A : ℝ)≤n by exact_mod_cast hnA).trans hx.1,
          hx.2.trans (show (n : ℝ)+1≤B by exact_mod_cast hnB)⟩
      have hyR : y∈Set.Icc (A : ℝ) (B : ℝ) :=
        ⟨(show (A : ℝ)≤n by exact_mod_cast hnA).trans hy.1,
          hy.2.trans (show (n : ℝ)+1≤B by exact_mod_cast hnB)⟩
      rw [integerIntervalClamp_eq hxR,integerIntervalClamp_eq hyR]
      exact hunit n hnA hnB x hx y hy

end
end AbelianTargets


