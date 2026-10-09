-- Prove2me | Definitions.Def_Nonadditivity_ChannelReindex
-- name    : Nonadditivity_ChannelReindex
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:22:47.081654+00:00
-- url     : https://prove2.me/theorems/0a2c05f6-5db9-4a4a-9b51-649cb87bbdbe
-- title:
--   Relabeling finite states and Kraus channels
-- statement:
--   Finite index equivalences relabel the rows and columns of density matrices and the input and output indices of Kraus channels. Relabeling preserves density-matrix entropy and commutes with the channel action. Reindexing the Kraus labels does not change the map, and an equivalence matching the Kraus matrices identifies the resulting channel maps. These operations let the construction use standard finite index types without changing its information quantities.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/ChannelReindex.lean#L27-L107

import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyProducts
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-!
# Channel reindexing and environment-coordinate identities

These are actual finite matrix identities. In particular, complementing a tensor
product and conjugating a complement commute without an assumed entropy law.
-/

noncomputable section

namespace Nonadditivity

open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

namespace Entropy

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

/-- Relabel an actual density matrix by a basis equivalence. -/
def DensityMatrix.reindex (ρ : DensityMatrix ι) (e : ι ≃ μ) : DensityMatrix μ where
  matrix := Matrix.reindex e e ρ.matrix
  positive := ρ.positive.submatrix e.symm
  normalized := by
    change (∑ j, ρ.matrix (e.symm j) (e.symm j)) = 1
    exact (e.symm.sum_comp (fun i => ρ.matrix i i)).trans ρ.normalized

/-- Relabeling preserves the actual von Neumann entropy, via characteristic roots. -/
theorem DensityMatrix.reindex_entropy (ρ : DensityMatrix ι) (e : ι ≃ μ) :
    (ρ.reindex e).vonNeumann = ρ.vonNeumann := by
  have hc : (ρ.reindex e).matrix.charpoly = ρ.matrix.charpoly :=
    Matrix.charpoly_reindex e ρ.matrix
  have he := (ρ.reindex e).positive.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hc, ρ.positive.isHermitian.roots_charpoly_eq_eigenvalues] at he
  have hs := congrArg (fun s : Multiset ℂ =>
    (s.map (fun z => z.re * Real.log z.re)).sum) he
  simp only [Multiset.map_map, Function.comp_def] at hs
  change (∑ i, ρ.weights i * Real.log (ρ.weights i)) =
    ∑ i, (ρ.reindex e).weights i * Real.log ((ρ.reindex e).weights i) at hs
  exact congrArg Neg.neg hs.symm

end Entropy

namespace Channels.KrausChannel

variable {ι ο κ μ ν η : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [Fintype κ]





/-- Relabel the input and output basis indices of an actual Kraus channel. -/
def reindex [Fintype μ] [DecidableEq μ] [Fintype ν]
    (T : Channels.KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) :
    Channels.KrausChannel μ ν κ where
  kraus := fun k => (T.kraus k).submatrix eo.symm ei.symm
  complete := by
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    calc
      (∑ k, ((T.kraus k).conjTranspose * T.kraus k).submatrix ei.symm ei.symm) =
          (∑ k, (T.kraus k).conjTranspose * T.kraus k).submatrix ei.symm ei.symm := by
        ext a b
        simp only [Matrix.sum_apply, Matrix.submatrix_apply]
      _ = 1 := by rw [T.complete]; exact Matrix.submatrix_one_equiv ei.symm

/-- The channel's reindexing is the concrete conjugation of its input/output coordinates. -/
theorem reindex_map [Fintype μ] [DecidableEq μ] [Fintype ν]
    (T : Channels.KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν)
    (X : Matrix ι ι ℂ) :
    (T.reindex ei eo).map (Matrix.reindex ei ei X) = Matrix.reindex eo eo (T.map X) := by
  simp only [map, reindex, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  ext a b
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]

/-- Kraus-index equivalences do not change the actual channel map. -/
theorem map_eq_of_kraus_equiv [Fintype η]
    (T : Channels.KrausChannel ι ο κ) (S : Channels.KrausChannel ι ο η)
    (e : κ ≃ η) (h : ∀ l, S.kraus l = T.kraus (e.symm l)) (X : Matrix ι ι ℂ) :
    S.map X = T.map X := by
  simp only [map, h]
  exact e.symm.sum_comp (fun k => T.kraus k * X * (T.kraus k).conjTranspose)

/-- Relabel the environment index; the represented channel is unchanged. -/
def reindexKraus [Fintype η] (T : Channels.KrausChannel ι ο κ) (e : κ ≃ η) :
    Channels.KrausChannel ι ο η where
  kraus := fun l => T.kraus (e.symm l)
  complete := (e.symm.sum_comp (fun k => (T.kraus k).conjTranspose * T.kraus k)).trans T.complete

@[simp] theorem reindexKraus_map [Fintype η] (T : Channels.KrausChannel ι ο κ)
    (e : κ ≃ η) (X : Matrix ι ι ℂ) : (T.reindexKraus e).map X = T.map X :=
  map_eq_of_kraus_equiv T _ e (fun _ => rfl) X

section FourFactorShuffle

variable {i₁ i₂ i₃ i₄ o₁ o₂ o₃ o₄ k₁ k₂ k₃ k₄ : Type*}
variable [Fintype i₁] [DecidableEq i₁] [Fintype i₂] [DecidableEq i₂]
variable [Fintype i₃] [DecidableEq i₃] [Fintype i₄] [DecidableEq i₄]
variable [Fintype o₁] [Fintype o₂] [Fintype o₃] [Fintype o₄]
variable [Fintype k₁] [Fintype k₂] [Fintype k₃] [Fintype k₄]



end FourFactorShuffle

end Channels.KrausChannel
end Nonadditivity


