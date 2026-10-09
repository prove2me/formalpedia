-- Prove2me | Definitions.Def_Nonadditivity_ChannelEntropy
-- name    : Nonadditivity_ChannelEntropy
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:34.863666+00:00
-- url     : https://prove2.me/theorems/68ddb1f0-b871-4f72-aa58-71b7ce7b4408
-- title:
--   Classical control, conditional inputs, and the Weyl extension
-- statement:
--   For finite classical labels and a finite Kraus channel family, the input density matrix is split into diagonal label blocks. Their traces are nonnegative weights summing to one; the conditional input is the normalized block when its weight is positive and a fixed density matrix at zero weight. The controlled output is the corresponding mixture. For positive output dimension $d$, the Weyl extension adds exactly $d^2$ labels and satisfies $\chi(T_{\mathrm W})=\log d-S_{\min}(T)$, with entropy and information in natural logarithm units here.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ChannelEntropy.lean#L29-L147

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_Weyl
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/







/-! # Entropy and Holevo information of measured-register extensions

The conditional states and their probabilities are constructed from the
actual diagonal blocks of the input. Entropy concavity is a proved theorem.
-/

noncomputable section

namespace Nonadditivity.Channels

open Entropy
open scoped BigOperators ComplexOrder Matrix

variable {ι ο κ ζ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο]
variable [Fintype κ] [Fintype ζ] [DecidableEq ζ]

def inputBlock (ρ : DensityMatrix (ζ × ι)) (z : ζ) : Matrix ι ι ℂ :=
  selector z * ρ.matrix * (selector z).conjTranspose

theorem inputBlock_positive (ρ : DensityMatrix (ζ × ι)) (z : ζ) :
    (inputBlock ρ z).PosSemidef := ρ.positive.mul_mul_conjTranspose_same _

def inputWeight (ρ : DensityMatrix (ζ × ι)) (z : ζ) : ℝ := (inputBlock ρ z).trace.re

theorem inputWeight_nonneg (ρ : DensityMatrix (ζ × ι)) (z : ζ) : 0 ≤ inputWeight ρ z :=
  positive_trace_re_nonneg _ (inputBlock_positive ρ z)

theorem inputWeight_sum (ρ : DensityMatrix (ζ × ι)) : ∑ z, inputWeight ρ z = 1 := by
  have ht : ∑ z, (inputBlock ρ z).trace = 1 := by
    calc
      (∑ z, (inputBlock ρ z).trace) =
          ∑ z, (ρ.matrix * ((selector z).conjTranspose * selector z)).trace := by
        apply Finset.sum_congr rfl
        intro z _
        unfold inputBlock
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = (ρ.matrix * (∑ z, (selector z).conjTranspose * selector z)).trace := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
      _ = 1 := by rw [selector_complete, Matrix.mul_one, ρ.normalized]
  have h := congrArg Complex.re ht
  simpa [inputWeight] using h

def conditionalInput [Nonempty ι] (ρ : DensityMatrix (ζ × ι)) (z : ζ) : DensityMatrix ι :=
  normalizePositive (inputBlock ρ z) (inputBlock_positive ρ z)

theorem inputWeight_smul_conditionalInput [Nonempty ι]
    (ρ : DensityMatrix (ζ × ι)) (z : ζ) :
    (inputWeight ρ z : ℂ) • (conditionalInput ρ z).matrix = inputBlock ρ z :=
  trace_smul_normalizePositive _ _

namespace KrausChannel

/-- Every controlled-channel output is the explicitly normalized mixture of
its branch outputs, including branches of probability zero. -/
theorem controlled_output_mixture [Nonempty ι]
    (T : ζ → KrausChannel ι ο κ) (ρ : DensityMatrix (ζ × ι)) :
    (controlled T).output ρ = DensityMatrix.mixture (inputWeight ρ)
      (inputWeight_nonneg ρ) (inputWeight_sum ρ)
      (fun z => (T z).output (conditionalInput ρ z)) := by
  apply DensityMatrix.ext
  simp only [output_matrix, DensityMatrix.mixture_matrix, controlled_map]
  apply Finset.sum_congr rfl
  intro z _
  rw [← map_smul, inputWeight_smul_conditionalInput]
  rfl

/-- A uniform lower output entropy bound survives measuring and discarding
the branch register. -/
theorem controlled_output_entropy_lower [Nonempty ι]
    (T : ζ → KrausChannel ι ο κ) {s : ℝ}
    (hentropy : ∀ z (ρ : DensityMatrix ι), s ≤ ((T z).output ρ).vonNeumann)
    (ρ : DensityMatrix (ζ × ι)) : s ≤ ((controlled T).output ρ).vonNeumann := by
  rw [controlled_output_mixture]
  have hconc := EntropyMixtures.densityMatrix_mixture_entropy_concave
    (inputWeight ρ) (inputWeight_nonneg ρ) (inputWeight_sum ρ)
    (fun z => (T z).output (conditionalInput ρ z))
  have hsum : s ≤ ∑ z, inputWeight ρ z * ((T z).output (conditionalInput ρ z)).vonNeumann := by
    calc
      s = ∑ z, inputWeight ρ z * s := by rw [← Finset.sum_mul, inputWeight_sum, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun z _ =>
        mul_le_mul_of_nonneg_left (hentropy z _) (inputWeight_nonneg ρ z))
  exact hsum.trans hconc

theorem outputUnitary_output (T : KrausChannel ι ο κ)
    (U : unitary (Matrix ο ο ℂ)) (ρ : DensityMatrix ι) :
    (T.outputUnitary U).output ρ = (T.output ρ).unitaryConjugate U := by
  apply DensityMatrix.ext
  exact T.outputUnitary_map U ρ.matrix

theorem outputUnitary_entropy (T : KrausChannel ι ο κ)
    (U : unitary (Matrix ο ο ℂ)) (ρ : DensityMatrix ι) :
    ((T.outputUnitary U).output ρ).vonNeumann = (T.output ρ).vonNeumann := by
  rw [outputUnitary_output, DensityMatrix.unitaryConjugate_entropy]

theorem covariantExtension_entropy_lower [Nonempty ι]
    (T : KrausChannel ι ο κ) (U : ζ → unitary (Matrix ο ο ℂ)) {s : ℝ}
    (hentropy : ∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann)
    (ρ : DensityMatrix (ζ × ι)) :
    s ≤ ((T.covariantExtension U).output ρ).vonNeumann := by
  apply controlled_output_entropy_lower
  intro z σ
  rw [outputUnitary_entropy]
  exact hentropy σ

/-- A concrete Weyl extension uses precisely `d²` classical labels. -/
def weylExtension {d : ℕ} [NeZero d] (T : KrausChannel ι (ZMod d) κ) :
    KrausChannel ((ZMod d × ZMod d) × ι) (ZMod d) ((ZMod d × ZMod d) × κ) :=
  T.covariantExtension Weyl.family

theorem weylExtension_holevo_lower {d : ℕ} [NeZero d] [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) (ρ : DensityMatrix ι) :
    Real.log d - (T.output ρ).vonNeumann ≤ T.weylExtension.holevo := by
  apply Weyl.orbit_information_lower_bound T.weylExtension.outputs (T.output ρ)
  intro q
  refine ⟨labelledState q ρ, ?_⟩
  change ((controlled (fun q => T.outputUnitary (Weyl.family q))).output
      (labelledState q ρ)) = _
  rw [controlled_output_labelled, outputUnitary_output]

/-- The complete single-use Shor/Weyl equality for a concrete Kraus channel.
No minimum-attaining input or entropy-concavity premise is assumed. -/
theorem weylExtension_holevo {d : ℕ} [NeZero d] [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) :
    T.weylExtension.holevo = Real.log d - T.minimumEntropy := by
  apply le_antisymm
  · have h := T.weylExtension.holevo_le_of_output_entropy
      (T.covariantExtension_entropy_lower Weyl.family
        (fun ρ => StateEnsembles.minimumEntropy_le (outputs := T.outputs) ⟨ρ, rfl⟩))
    simpa only [ZMod.card] using h
  · have hglb : Real.log d - T.weylExtension.holevo ≤ T.minimumEntropy := by
      apply le_csInf (T.outputs_nonempty.image _)
      rintro _ ⟨σ, ⟨ρ, rfl⟩, rfl⟩
      have h := T.weylExtension_holevo_lower ρ
      linarith
    linarith

end KrausChannel
end Nonadditivity.Channels


