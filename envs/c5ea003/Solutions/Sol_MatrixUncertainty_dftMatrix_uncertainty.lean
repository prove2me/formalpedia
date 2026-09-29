-- Prove2me | solution 1 for MatrixUncertainty.dftMatrix_uncertainty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:05:14.053167+00:00
-- url     : https://prove2.me/submissions/3f4a493c-429b-4bb0-9984-0f4c28f11eb9

-- Sol generated from Bridges/MatrixUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_MatrixUncertainty
import Theorems.Thm_MatrixUncertainty_abstract_uncertainty
import Theorems.Thm_MatrixUncertainty_dftMatrix_mulVec
import Theorems.Thm_MatrixUncertainty_invDftMatrix_mul_dftMatrix
import Theorems.Thm_MatrixUncertainty_norm_dftMatrix_entry
import Theorems.Thm_MatrixUncertainty_norm_invDftMatrix_entry

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










/-! ## Boundedness is essential

The abstract principle uses two hypotheses. Invertibility alone is not enough: the identity
matrix is invertible with `B = C = 1`, but the bound it produces, `1 ≤ |supp v| * |supp v|`, is
vacuous. Concretely, an invertible transform can map a delta to a delta, so no uncertainty bound
better than `1` can follow from invertibility alone; the gain in the Fourier case comes entirely
from the smallness `C = 1/N` of the inverse entries. -/





open MatrixUncertainty in
theorem solution(Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) :
    (N : ℝ) ≤ (vsupport Φ).card * (vsupport (𝓕 Φ)).card := by
  have h := abstract_uncertainty (dftMatrix N) (invDftMatrix N) invDftMatrix_mul_dftMatrix
    1 (N : ℝ)⁻¹ norm_dftMatrix_entry norm_invDftMatrix_entry Φ hΦ
  rw [dftMatrix_mulVec] at h
  have hN : (0 : ℝ) < N := by
    have := NeZero.ne N
    positivity
  rw [one_mul] at h
  calc (N : ℝ) = N * 1 := by ring
    _ ≤ N * ((N : ℝ)⁻¹ * ((vsupport Φ).card * (vsupport (𝓕 Φ)).card)) := by
        exact mul_le_mul_of_nonneg_left h hN.le
    _ = (vsupport Φ).card * (vsupport (𝓕 Φ)).card := by
        field_simp
