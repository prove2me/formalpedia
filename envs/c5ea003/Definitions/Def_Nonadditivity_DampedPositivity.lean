-- Prove2me | Definitions.Def_Nonadditivity_DampedPositivity
-- name    : Nonadditivity_DampedPositivity
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:44:04.753308+00:00
-- url     : https://prove2.me/theorems/cd1b5621-2d52-4e40-a4d2-20f6a1f4eb68
-- title:
--   Strictly positive information after invertible damping
-- statement:
--   Let $T$ be a finite Kraus channel with positive output dimension. If a Hermitian filter $F$ satisfies $I-F^2\succeq0$, has a left inverse $G$ with $GF=I$, and $T$ has an output different from the maximally mixed state, then the switch/Weyl conversion of the damped channel has strictly positive Holevo information in bits. The bundle constructs the required nonuniform damped output and applies the result to unitary block channels with $K\ge2$ branches and at least one factor.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/DampedPositivity.lean#L28-L132

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_BlockScalars
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_DampedChannel
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_HolevoBits
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PositiveHolevo
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_Scalar
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_StrictEntropy
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # Invertible damping preserves a nonuniform output

The input is pulled back through a left inverse and renormalized. Its output
is a strictly positive multiple of the original output plus uniform noise.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.DampedPositivity

open Entropy Channels Channels.KrausChannel DampedChannel
open scoped BigOperators Matrix ComplexOrder

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

/-- Pulling a state back through an invertible filter gives its original
output, mixed with uniform noise with a strictly positive retained weight. -/
theorem exists_damped_output_mixture (T : KrausChannel ι ο κ)
    (F G : Matrix ι ι ℂ) (hF : F.IsHermitian)
    (hres : (1-F*F).PosSemidef) (hGF : G*F=1) (ρ : DensityMatrix ι) :
    ∃ (σ : DensityMatrix ι) (c : ℂ), c ≠ 0 ∧
      ((damped T F hF hres).output σ).matrix =
        c • (T.output ρ).matrix + (1-c) • (maximallyMixed ο).matrix := by
  let X := G.conjTranspose * ρ.matrix * G
  have hX : X.PosSemidef := ρ.positive.conjTranspose_mul_mul_same G
  have hFG : F * G.conjTranspose = 1 := by
    have hh := congrArg Matrix.conjTranspose hGF
    simpa only [Matrix.conjTranspose_mul, hF.eq, Matrix.conjTranspose_one] using hh
  have hrecover : F * X * F = ρ.matrix := by
    calc
      F * X * F = (F * G.conjTranspose) * ρ.matrix * (G * F) := by
        simp only [X, Matrix.mul_assoc]
      _ = ρ.matrix := by rw [hFG, hGF, Matrix.one_mul, Matrix.mul_one]
  have htr : X.trace.re ≠ 0 := by
    intro hh
    have ht : X.trace = 0 := by rw [← positive_trace_real X hX, hh]; simp
    have hz := hX.trace_eq_zero_iff.mp ht
    have hr : ρ.matrix = 0 := by simpa [hz] using hrecover.symm
    have hn := ρ.normalized
    rw [hr, Matrix.trace_zero] at hn
    exact zero_ne_one hn
  let σ := normalizePositive X hX
  let c : ℂ := ((X.trace.re)⁻¹ : ℝ)
  have hc : c ≠ 0 := by
    change (((X.trace.re)⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero htr
  have hσ : σ.matrix = c • X := by simp [σ, normalizePositive, htr, c]
  have hretain : F * σ.matrix * F = c • ρ.matrix := by
    rw [hσ, Matrix.mul_smul, Matrix.smul_mul, hrecover]
  have htrace : ((1-F*F)*σ.matrix).trace = 1-c := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, σ.normalized]
    have ht : (F*F*σ.matrix).trace = c := by
      rw [← Matrix.trace_mul_cycle F σ.matrix F, hretain, Matrix.trace_smul,
        ρ.normalized, smul_eq_mul, mul_one]
    rw [ht]
  refine ⟨σ, c, hc, ?_⟩
  rw [output_matrix, damped_map, hretain, KrausChannel.map_smul, htrace]
  congr 1
  simp only [maximallyMixed, smul_smul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_natCast]
  congr 1
  ring

theorem exists_damped_output_ne_maximallyMixed (T : KrausChannel ι ο κ)
    (F G : Matrix ι ι ℂ) (hF : F.IsHermitian)
    (hres : (1-F*F).PosSemidef) (hGF : G*F=1)
    (hT : ∃ ρ : DensityMatrix ι, T.output ρ ≠ maximallyMixed ο) :
    ∃ σ : DensityMatrix ι, (damped T F hF hres).output σ ≠ maximallyMixed ο := by
  obtain ⟨ρ, hρ⟩ := hT
  obtain ⟨σ, c, hc, he⟩ := exists_damped_output_mixture T F G hF hres hGF ρ
  refine ⟨σ, fun hh => hρ ?_⟩
  apply DensityMatrix.ext
  have hh' := congrArg DensityMatrix.matrix hh
  rw [he] at hh'
  have heq : c • (T.output ρ).matrix - c • (maximallyMixed ο).matrix = 0 := by
    calc
      _ = (c • (T.output ρ).matrix + (1-c) • (maximallyMixed ο).matrix) -
          (maximallyMixed ο).matrix := by rw [sub_smul, one_smul]; abel
      _ = 0 := sub_eq_zero.mpr hh'
  exact (smul_right_injective _ hc) (sub_eq_zero.mp heq)

theorem converted_holevo_pos_of_nonuniform {d : ℕ} [NeZero d]
    (T : KrausChannel ι (ZMod d) κ)
    (hT : ∃ ρ : DensityMatrix ι, T.output ρ ≠ maximallyMixed (ZMod d)) :
    0 < (Conversion.converted T).holevo := by
  obtain ⟨ρ, hρ⟩ := hT
  have hs := (T.output ρ).vonNeumann_lt_log_card_of_ne_maximallyMixed hρ
  have hm : T.minimumEntropy ≤ (T.output ρ).vonNeumann :=
    StateEnsembles.minimumEntropy_le ⟨ρ,rfl⟩
  rw [Conversion.converted_holevo]
  simp only [ZMod.card] at hs
  linarith

theorem converted_damped_holevoBits_pos {d : ℕ} [NeZero d]
    (T : KrausChannel ι (ZMod d) κ) (F G : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (hGF : G*F=1)
    (hT : ∃ ρ : DensityMatrix ι, T.output ρ ≠ maximallyMixed (ZMod d)) :
    0 < (Conversion.converted (damped T F hF hres)).holevoBits := by
  apply div_pos _ Scalar.log_two_pos
  exact converted_holevo_pos_of_nonuniform _
    (exists_damped_output_ne_maximallyMixed T F G hF hres hGF hT)

/-- The concrete block construction retains a strictly positive Holevo
denominator after any invertible damping filter. -/
theorem converted_damped_block_holevoBits_pos {K : ℕ} [NeZero K] (hK : 2 ≤ K)
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ)) {n : ℕ} (hn : 1 ≤ n)
    (F G : Matrix (TensorChainIndex ι n) (TensorChainIndex ι n) ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (hGF : G*F=1) :
    0 < (Conversion.converted
      (damped (BlockConstruction.blockChannel U n) F hF hres)).holevoBits := by
  apply converted_damped_holevoBits_pos _ F G hF hres hGF
  obtain ⟨ρ, hρ⟩ := PositiveHolevo.exists_block_entropy_le hK U n
  refine ⟨ρ, fun he => ?_⟩
  rw [he, maximallyMixed_entropy] at hρ
  simp only [ZMod.card, Nat.cast_pow, Real.log_pow] at hρ
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hKp : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hp : 0 < (n : ℝ) * (2 * Real.log 2 / (K : ℝ)) :=
    mul_pos hnp (div_pos (mul_pos (by norm_num) Scalar.log_two_pos) hKp)
  nlinarith

end Nonadditivity.DampedPositivity


