-- Prove2me | solution 1 for MatrixUncertainty.abstract_uncertainty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:03:55.513606+00:00
-- url     : https://prove2.me/submissions/44228cea-525c-4868-abfe-c44e3d2d1a22

-- Sol generated from Bridges/MatrixUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_MatrixUncertainty
import Theorems.Thm_MatrixUncertainty_norm_mulVec_le

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
theorem solution(T T' : Matrix n n ℂ) (hinv : T' * T = 1)
    (B C : ℝ) (hB : ∀ i j, ‖T i j‖ ≤ B) (hC : ∀ i j, ‖T' i j‖ ≤ C)
    (v : n → ℂ) (hv : v ≠ 0) :
    1 ≤ B * C * ((vsupport v).card * (vsupport (T.mulVec v)).card) := by
  classical
  obtain ⟨x₀⟩ : Nonempty n := by
    by_contra h
    exact hv (funext fun j => absurd ⟨j⟩ h)
  obtain ⟨j₀, -, hj₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset n) (fun j => ‖v j‖) ⟨x₀, mem_univ _⟩
  set M : ℝ := ‖v j₀‖ with hMdef
  have hM : ∀ j, ‖v j‖ ≤ M := fun j => hj₀ j (mem_univ j)
  have hMpos : 0 < M := by
    rcases lt_or_eq_of_le (norm_nonneg (v j₀)) with h | h
    · exact h
    · exfalso
      apply hv
      funext j
      have : ‖v j‖ ≤ 0 := by rw [hMdef, ← h] at hM; exact hM j
      simpa using le_antisymm this (norm_nonneg _)
  have hBpos : 0 ≤ B := le_trans (norm_nonneg _) (hB x₀ x₀)
  have hCpos : 0 ≤ C := le_trans (norm_nonneg _) (hC x₀ x₀)
  -- the image is bounded entrywise
  have h1 : ∀ i, ‖T.mulVec v i‖ ≤ B * (vsupport v).card * M :=
    norm_mulVec_le T B M hB hBpos v hM
  -- reconstructing `v` from its image bounds `M` in terms of the two support sizes
  have hrec : T'.mulVec (T.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h2 : ‖T'.mulVec (T.mulVec v) j₀‖
      ≤ C * (vsupport (T.mulVec v)).card * (B * (vsupport v).card * M) :=
    norm_mulVec_le T' C _ hC hCpos (T.mulVec v) h1 j₀
  rw [hrec] at h2
  have h3 : M ≤ C * (vsupport (T.mulVec v)).card * (B * (vsupport v).card * M) := h2
  have h4 : 1 * M ≤ (B * C * ((vsupport v).card * (vsupport (T.mulVec v)).card)) * M := by
    nlinarith [h3]
  exact le_of_mul_le_mul_right h4 hMpos
