-- Prove2me | solution 1 for MatrixUncertainty.invDftMatrix_mul_dftMatrix
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:53:53.891929+00:00
-- url     : https://prove2.me/submissions/fad55774-3e60-41de-8da3-29ad1643500a

-- Sol generated from Bridges/MatrixUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_MatrixUncertainty
import Theorems.Thm_MatrixUncertainty_dftMatrix_mulVec

/-!
# An abstract uncertainty principle for invertible bounded transforms

`Catalog/Bridges/FourierAsFunctor.lean` disproved that contravariant duality by itself implies
any uncertainty bound, and `Catalog/Bridges/FourierFunctorUncertainty.lean` proved the
Donoho–Stark bound for the discrete Fourier transform. This file isolates the *exact* extra
structure that makes an uncertainty principle work: an invertible transform whose matrix entries
and whose inverse's matrix entries are uniformly bounded.

## Main results

* `MatrixUncertainty.abstract_uncertainty` : if `T' * T = 1`, `‖T i j‖ ≤ B` and `‖T' i j‖ ≤ C`,
  then every nonzero `v` satisfies `1 ≤ B * C * |supp v| * |supp (T v)|`. Neither invertibility
  alone nor boundedness alone suffices; both hypotheses are used.
* `MatrixUncertainty.dftMatrix_uncertainty` : the Fourier case `B = 1`, `C = 1 / N` of the
  abstract theorem recovers the Donoho–Stark bound `N ≤ |supp Φ| * |supp 𝓕Φ|` from the abstract
  principle, giving a second, structurally different proof of it.
* `MatrixUncertainty.uncertainty_needs_boundedness` : a certified counterexample showing the
  boundedness hypothesis cannot be dropped — an invertible transform (a rescaled projection-free
  triangular matrix) maps a delta to a delta, so support product `1` is possible.
-/

open Finset Matrix ZMod

open MatrixUncertainty


variable {n : Type*} [Fintype n] [DecidableEq n]






/-! ## The Fourier transform as an instance of the abstract principle -/


variable {N : ℕ} [NeZero N]




theorem invDftMatrix_mulVec (Ψ : ZMod N → ℂ) : (invDftMatrix N).mulVec Ψ = 𝓕⁻ Ψ := by
  funext k
  rw [ZMod.invDFT_apply, Matrix.mulVec, dotProduct]
  simp [invDftMatrix, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]






/-! ## Boundedness is essential

The abstract principle uses two hypotheses. Invertibility alone is not enough: the identity
matrix is invertible with `B = C = 1`, but the bound it produces, `1 ≤ |supp v| * |supp v|`, is
vacuous. Concretely, an invertible transform can map a delta to a delta, so no uncertainty bound
better than `1` can follow from invertibility alone; the gain in the Fourier case comes entirely
from the smallness `C = 1/N` of the inverse entries. -/





open MatrixUncertainty in
theorem solution: invDftMatrix N * dftMatrix N = 1 := by
  ext i j
  have h : ((invDftMatrix N) * (dftMatrix N)).mulVec (Pi.single j (1 : ℂ) : ZMod N → ℂ) i
      = (Pi.single j (1 : ℂ) : ZMod N → ℂ) i := by
    rw [← Matrix.mulVec_mulVec, dftMatrix_mulVec, invDftMatrix_mulVec]
    simp
  rw [Matrix.mulVec_single] at h
  rw [Matrix.one_apply]
  simpa [Pi.single_apply, eq_comm] using h
