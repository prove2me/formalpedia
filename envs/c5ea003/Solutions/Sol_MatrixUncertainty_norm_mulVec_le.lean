-- Prove2me | solution 1 for MatrixUncertainty.norm_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:52:42.778148+00:00
-- url     : https://prove2.me/submissions/635fa461-c8f1-4136-b8d2-af0e9815148b

-- Sol generated from Bridges/MatrixUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_MatrixUncertainty
import Theorems.Thm_MatrixUncertainty_mem_vsupport

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
omit [DecidableEq n] in
theorem solution(T : Matrix n n ℂ) (B M : ℝ) (hB : ∀ i j, ‖T i j‖ ≤ B)
    (hBpos : 0 ≤ B) (v : n → ℂ) (hM : ∀ j, ‖v j‖ ≤ M) (i : n) :
    ‖T.mulVec v i‖ ≤ B * (vsupport v).card * M := by
  classical
  rw [Matrix.mulVec, dotProduct]
  have hsum : ∑ j, T i j * v j = ∑ j ∈ vsupport v, T i j * v j := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    have : v x = 0 := by
      by_contra h
      exact hx (mem_vsupport.2 h)
    simp [this]
  rw [hsum]
  calc ‖∑ j ∈ vsupport v, T i j * v j‖
      ≤ ∑ j ∈ vsupport v, ‖T i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ vsupport v, B * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hB i j) (hM j) (norm_nonneg _) hBpos
    _ = B * (vsupport v).card * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
