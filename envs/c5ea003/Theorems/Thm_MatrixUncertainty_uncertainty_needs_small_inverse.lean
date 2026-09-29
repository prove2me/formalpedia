-- Prove2me | Theorems.Thm_MatrixUncertainty_uncertainty_needs_small_inverse
-- name    : MatrixUncertainty.uncertainty_needs_small_inverse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:56:06.123863+00:00
-- url     : https://prove2.me/theorems/1958e0a5-5901-4a32-8ed6-617199b657ce
-- title:
--   The identity transform on `ZMod 4` is invertible with unit-bounded entries in both
-- statement:
--   The identity transform on `ZMod 4` is invertible with unit-bounded entries in both
--   directions, yet a delta vector has support product `1`. Hence invertibility together with mere
--   boundedness by `1` cannot give any bound above `1`: the strength of the Fourier uncertainty
--   principle really comes from the `1/N` scale of the inverse entries, so the constant `B * C` in
--   `abstract_uncertainty` cannot be removed.
--
--   ```lean
--   theorem MatrixUncertainty.uncertainty_needs_small_inverse:
--       ∃ (T T' : Matrix (ZMod 4) (ZMod 4) ℂ) (v : ZMod 4 → ℂ),
--         T' * T = 1 ∧ v ≠ 0 ∧ (∀ i j, ‖T i j‖ ≤ 1) ∧ (∀ i j, ‖T' i j‖ ≤ 1) ∧
--           (vsupport v).card * (vsupport (T.mulVec v)).card = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MatrixUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MatrixUncertainty.lean#L185

-- Thm stub generated from Bridges/MatrixUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Definitions.Def_Bridges_MatrixUncertainty

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

theorem MatrixUncertainty.uncertainty_needs_small_inverse:
    ∃ (T T' : Matrix (ZMod 4) (ZMod 4) ℂ) (v : ZMod 4 → ℂ),
      T' * T = 1 ∧ v ≠ 0 ∧ (∀ i j, ‖T i j‖ ≤ 1) ∧ (∀ i j, ‖T' i j‖ ≤ 1) ∧
        (vsupport v).card * (vsupport (T.mulVec v)).card = 1 := by sorry
