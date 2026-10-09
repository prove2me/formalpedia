-- Prove2me | Definitions.Def_Nonadditivity_ConjugateChannel
-- name    : Nonadditivity_ConjugateChannel
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:33:19.168976+00:00
-- url     : https://prove2.me/theorems/482fbc99-4273-46d8-99aa-99ecedcd2b9a
-- title:
--   Conjugate quantum channels preserve output entropy
-- statement:
--   Entrywise complex conjugation is an involution on finite density matrices and transports a Kraus channel to its conjugate. Applying the conjugate channel to the conjugate input gives the conjugate of the original output, whose entropy is unchanged. Involutivity then yields the output entropy correspondence for arbitrary input states. The channel extensionality principle identifies channels with equal Kraus families.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ConjugateChannel.lean#L25-L83

import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# Conjugate channels and minimum output entropy

The conjugate input operation is a proved involution on actual density
matrices. Conjugate channels have identical output entropy ranges, so their
minimum output entropies agree. No entropy-preservation condition is assumed.
-/

noncomputable section

namespace Nonadditivity.Entropy

open scoped Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a Hermitian state, transpose equals entrywise conjugation. -/
theorem DensityMatrix.conjugate_matrix_eq_map_star (ρ : DensityMatrix ι) :
    ρ.conjugate.matrix = ρ.matrix.map star := by
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M j i) ρ.positive.isHermitian.eq
  simpa [DensityMatrix.conjugate, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.star_apply] using h.symm

@[simp] theorem DensityMatrix.conjugate_conjugate (ρ : DensityMatrix ι) :
    ρ.conjugate.conjugate = ρ := by
  apply DensityMatrix.ext
  simp [DensityMatrix.conjugate]

end Nonadditivity.Entropy

namespace Nonadditivity.Channels.KrausChannel

open scoped Matrix ComplexOrder
open Nonadditivity.Entropy

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype ο] [DecidableEq ο] [Fintype κ]

omit [DecidableEq ο] in
@[ext] theorem ext {T S : KrausChannel ι ο κ} (h : T.kraus = S.kraus) : T = S := by
  cases T
  cases S
  cases h
  rfl

omit [DecidableEq ο] in
@[simp] theorem conjugate_conjugate (T : KrausChannel ι ο κ) :
    T.conjugate.conjugate = T := by
  apply ext
  funext k
  ext i j
  simp [conjugate, Matrix.map_apply]

/-- The concrete conjugate-channel map acts on actual conjugate states. -/
@[simp] theorem conjugate_output (T : KrausChannel ι ο κ) (ρ : DensityMatrix ι) :
    T.conjugate.output ρ.conjugate = (T.output ρ).conjugate := by
  apply DensityMatrix.ext
  rw [output_matrix, ρ.conjugate_matrix_eq_map_star, conjugate_map,
    (T.output ρ).conjugate_matrix_eq_map_star, output_matrix]

/-- The conjugate channel and original channel have equal entropy on
corresponding conjugate inputs. -/
@[simp] theorem conjugate_output_entropy (T : KrausChannel ι ο κ)
    (ρ : DensityMatrix ι) :
    (T.conjugate.output ρ.conjugate).vonNeumann = (T.output ρ).vonNeumann := by
  rw [conjugate_output, DensityMatrix.conjugate_entropy]

/-- Every input of the conjugate channel corresponds to a conjugate input
of the original channel; conjugation is surjective rather than an assumption. -/
theorem conjugate_output_entropy_all (T : KrausChannel ι ο κ)
    (ρ : DensityMatrix ι) :
    (T.conjugate.output ρ).vonNeumann = (T.output ρ.conjugate).vonNeumann := by
  simpa only [DensityMatrix.conjugate_conjugate] using
    conjugate_output_entropy T ρ.conjugate







end Nonadditivity.Channels.KrausChannel


