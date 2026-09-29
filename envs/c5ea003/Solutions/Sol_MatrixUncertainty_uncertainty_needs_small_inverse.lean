-- Prove2me | solution 1 for MatrixUncertainty.uncertainty_needs_small_inverse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:05:14.567751+00:00
-- url     : https://prove2.me/submissions/5e14cb1f-2304-4f5f-8903-47cc84d5eb4b

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
theorem solution:
    ∃ (T T' : Matrix (ZMod 4) (ZMod 4) ℂ) (v : ZMod 4 → ℂ),
      T' * T = 1 ∧ v ≠ 0 ∧ (∀ i j, ‖T i j‖ ≤ 1) ∧ (∀ i j, ‖T' i j‖ ≤ 1) ∧
        (vsupport v).card * (vsupport (T.mulVec v)).card = 1 := by
  classical
  refine ⟨1, 1, Pi.single (0 : ZMod 4) (1 : ℂ), by simp, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h (0 : ZMod 4)
    simp at this
  · intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · have hone : Matrix.mulVec (1 : Matrix (ZMod 4) (ZMod 4) ℂ) (Pi.single (0 : ZMod 4) (1 : ℂ))
        = Pi.single (0 : ZMod 4) (1 : ℂ) := Matrix.one_mulVec _
    have hsupp : vsupport (Pi.single (0 : ZMod 4) (1 : ℂ)) = {0} := by
      ext k
      simp only [mem_vsupport, Finset.mem_singleton]
      constructor
      · intro h
        by_contra hk
        exact h (Pi.single_eq_of_ne hk 1)
      · rintro rfl
        simp
    rw [hone, hsupp]
    simp
