-- Prove2me | Definitions.Def_BenchmarkRelations
-- name    : BenchmarkRelations
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T06:47:14.767744+00:00
-- url     : https://prove2.me/theorems/b62d4f43-a4e1-4bef-9811-4d87b06a39fa
-- title:
--   Benchmark relations, reductions, operators and unitary representations
-- statement:
--   The shared interfaces use real-sequence difference relations, the full $\mathbb F_2$ shift, countable products and jumps, actual Cantor probability measures and mutual absolute continuity, and genuine bounded operators and unitary representations on $\ell^2(\mathbb N;\mathbb C)$. Reductions require measurability and preservation and reflection on every pair. Operator and representation Borel structures are explicitly induced by pointwise norm convergence. The final six propositions name the exact target comparisons without assuming or proving them.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, supplied Benchmark.tex, Section 1; source SHA256 c3c80147a17922e19044935df97b27a2a2a0be5f86665e0869d6a376250d6330; repository designated by the author: https://github.com/RayjunWang/Benchmark. Definitions from Sections 1 and 2.

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.GroupTheory.FreeGroup.Basic

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace BenchmarkComparisons

abbrev Sequences := ℕ → ℝ
abbrev Cantor := ℕ → Bool
abbrev FreeTwo := FreeGroup (Fin 2)
abbrev ShiftSpace := FreeTwo → Bool
abbrev Hilbert := lp (fun _ : ℕ => ℂ) 2
abbrev BoundedOperator := Hilbert →L[ℂ] Hilbert
abbrev Unitary := Hilbert ≃ₗᵢ[ℂ] Hilbert

def BorelReduces {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x y, E x y ↔ F (f x) (f y)

def Incomparable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ¬ BorelReduces E F ∧ ¬ BorelReduces F E

def ProductRelation {X : Type*} (E : X → X → Prop) (x y : ℕ → X) : Prop :=
  ∀ n, E (x n) (y n)

def Jump {X : Type*} (E : X → X → Prop) (x y : ℕ → X) : Prop :=
  (∀ i, ∃ j, E (x i) (y j)) ∧ (∀ j, ∃ i, E (x i) (y j))

def EInfinity (x y : ShiftSpace) : Prop :=
  ∃ g : FreeTwo, ∀ h : FreeTwo, y h = x (g⁻¹ * h)

def LpDifference (p : ℝ) (x y : Sequences) : Prop :=
  Summable (fun n => |x n - y n| ^ p)

def NullDifference (x y : Sequences) : Prop :=
  Tendsto (fun n => x n - y n) atTop (𝓝 0)

def BoundedDifference (x y : Sequences) : Prop :=
  ∃ C : ℝ, ∀ n, |x n - y n| ≤ C

def ExtendedLpDifference (p : WithTop ℝ) (x y : Sequences) : Prop :=
  match p with
  | ⊤ => BoundedDifference x y
  | (r : ℝ) => LpDifference r x y

def MeasureEquivalent (μ ν : ProbabilityMeasure Cantor) : Prop :=
  (μ : Measure Cantor) ≪ (ν : Measure Cantor) ∧
    (ν : Measure Cantor) ≪ (μ : Measure Cantor)

def OperatorEquivalent (T S : BoundedOperator) : Prop :=
  ∃ U : Unitary, ∀ v : Hilbert, U (T v) = S (U v)

def operatorStrongTopology : TopologicalSpace BoundedOperator :=
  TopologicalSpace.induced (fun T : BoundedOperator => fun v : Hilbert => T v) inferInstance

def operatorBorel : MeasurableSpace BoundedOperator :=
  @borel BoundedOperator operatorStrongTopology

structure Representation (Γ : Type*) [Group Γ] where
  operator : Γ → Unitary
  map_one : ∀ v : Hilbert, operator 1 v = v
  map_mul : ∀ g h : Γ, ∀ v : Hilbert, operator (g * h) v = operator g (operator h v)

def representationStrongTopology (Γ : Type*) [Group Γ] :
    TopologicalSpace (Representation Γ) :=
  TopologicalSpace.induced
    (fun ρ : Representation Γ => fun g : Γ => fun v : Hilbert => ρ.operator g v) inferInstance

def representationBorel (Γ : Type*) [Group Γ] : MeasurableSpace (Representation Γ) :=
  @borel (Representation Γ) (representationStrongTopology Γ)

def RepresentationEquivalent {Γ : Type*} [Group Γ] (ρ σ : Representation Γ) : Prop :=
  ∃ U : Unitary, ∀ g : Γ, ∀ v : Hilbert, U (ρ.operator g v) = σ.operator g (U v)

def BorelReducesWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, @Measurable X Y mX mY f ∧ ∀ x y, E x y ↔ F (f x) (f y)

def BorelBireducibleWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  BorelReducesWith mX mY E F ∧ BorelReducesWith mY mX F E

def BorelStrictlyReducesWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  BorelReducesWith mX mY E F ∧ ¬ BorelReducesWith mY mX F E

def CountableComparisons : Prop :=
  BorelReduces (ProductRelation EInfinity) NullDifference ∧
    ∀ p : ℝ, 1 ≤ p → Incomparable EInfinity (LpDifference p)

def ExponentThreshold : Prop :=
  ∀ p : WithTop ℝ, (1 : WithTop ℝ) ≤ p →
    (BorelReduces (ExtendedLpDifference p) MeasureEquivalent ↔ p ≤ (2 : WithTop ℝ))

def NullMeasureObstruction : Prop :=
  ¬ BorelReduces NullDifference MeasureEquivalent

def JumpObstructions : Prop :=
  ¬ BorelReduces NullDifference (Jump BoundedDifference) ∧
    ¬ BorelReduces MeasureEquivalent (Jump BoundedDifference)

def OperatorStrictComparison : Prop :=
  BorelStrictlyReducesWith inferInstance operatorBorel MeasureEquivalent OperatorEquivalent

def RepresentationComparisons : Prop :=
  BorelBireducibleWith (representationBorel (Multiplicative ℤ)) inferInstance
      RepresentationEquivalent MeasureEquivalent ∧
  BorelStrictlyReducesWith inferInstance (representationBorel (FreeGroup ℕ))
      MeasureEquivalent RepresentationEquivalent ∧
  BorelBireducibleWith (representationBorel (FreeGroup ℕ)) operatorBorel
      RepresentationEquivalent OperatorEquivalent

end BenchmarkComparisons


