-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularClass
-- name    : AnalyticCombinatorics_Ch7_SingularityApp_TwoRegularClass
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:47:04.836889+00:00
-- url     : https://prove2.me/theorems/b587ce15-f779-4250-a1f9-bd3fcf2030c9
-- title:
--   Two Regular Class
-- statement:
--   The mathematical objects and operations are specified by the following source definitions.
--
--   ```lean
--   def FullCyclePerm (n : ℕ) : Type :=
--     {σ : Equiv.Perm (Fin n) // σ.cycleType = {n}}
--   ```
--
--   ```lean
--   abbrev UndirectedCycle (n : ℕ) : Type :=
--     Quotient (AddAction.orbitRel Bool (FullCyclePerm n))
--   ```
--
--   ```lean
--   def undirectedCycleClass : CombClass where
--     Obj n := if 3 ≤ n then UndirectedCycle n else Fin 0
--     finObj n := by
--       classical
--       by_cases h : 3 ≤ n
--       · rw [if_pos h]
--         infer_instance
--       · rw [if_neg h]
--         infer_instance
--   ```
--
--   ```lean
--   def twoRegularClass : CombClass :=
--     undirectedCycleClass.set
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/TwoRegularClass.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Mathlib
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Combinatorics.Enumerative.Composition

namespace AnalyticCombinatorics.Ch5.Meromorphic.Alignments end AnalyticCombinatorics.Ch5.Meromorphic.Alignments

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Genuine labelled class of two-regular graphs

A two-regular labelled graph is a labelled `SET` of undirected cycles of
length at least three.  The cycle carried by one block is modelled as a full
cycle permutation on the block labels, modulo reversing the orientation.
-/

open Complex Filter Asymptotics
open scoped BigOperators PowerSeries Topology

noncomputable section

namespace TwoRegularClass

open AnalyticCombinatorics.Ch1
open AnalyticCombinatorics.Ch5.Meromorphic.Alignments

/-- Directed full cycles on `Fin n`, represented as permutations with cycle type `{n}`. -/
def FullCyclePerm (n : ℕ) : Type :=
  {σ : Equiv.Perm (Fin n) // σ.cycleType = {n}}

instance (n : ℕ) : Fintype (FullCyclePerm n) := by
  classical
  unfold FullCyclePerm
  infer_instance

/-- Reversing the orientation of a directed full cycle. -/
def fullCycleReverse {n : ℕ} (c : FullCyclePerm n) : FullCyclePerm n :=
  ⟨c.1⁻¹, by rw [Equiv.Perm.cycleType_inv, c.2]⟩

lemma fullCycleReverse_reverse {n : ℕ} (c : FullCyclePerm n) :
    fullCycleReverse (fullCycleReverse c) = c := by
  apply Subtype.ext
  simp [fullCycleReverse]

instance fullCyclePermVAddBool (n : ℕ) : VAdd Bool (FullCyclePerm n) where
  vadd b c := if b then fullCycleReverse c else c

instance fullCyclePermAddActionBool (n : ℕ) : AddAction Bool (FullCyclePerm n) where
  zero_vadd c := by
    rfl
  add_vadd b₁ b₂ c := by
    cases b₁ <;> cases b₂
    · rfl
    · rfl
    · rfl
    · change c = fullCycleReverse (fullCycleReverse c)
      rw [fullCycleReverse_reverse]

/-- Undirected cycle structures on `Fin n`: full directed cycles modulo reversal. -/
abbrev UndirectedCycle (n : ℕ) : Type :=
  Quotient (AddAction.orbitRel Bool (FullCyclePerm n))

instance (n : ℕ) : Fintype (UndirectedCycle n) := by
  classical
  unfold UndirectedCycle
  infer_instance

/-- One-block class of undirected cycles of length at least three. -/
def undirectedCycleClass : CombClass where
  Obj n := if 3 ≤ n then UndirectedCycle n else Fin 0
  finObj n := by
    classical
    by_cases h : 3 ≤ n
    · rw [if_pos h]
      infer_instance
    · rw [if_neg h]
      infer_instance

/-- The genuine labelled class of two-regular graphs: a labelled set of undirected cycles. -/
def twoRegularClass : CombClass :=
  undirectedCycleClass.set

/-! ### Complex analytic bridge to the singularity-analysis file -/

end TwoRegularClass


