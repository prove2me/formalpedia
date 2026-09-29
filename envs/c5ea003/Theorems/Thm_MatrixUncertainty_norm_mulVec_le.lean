-- Prove2me | Theorems.Thm_MatrixUncertainty_norm_mulVec_le
-- name    : MatrixUncertainty.norm_mulVec_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:03:23.336728+00:00
-- url     : https://prove2.me/theorems/16da788d-798b-418e-be9a-a66329a6d2dd
-- title:
--   A matrix with entries bounded by `B` maps a vector with small support and sup norm `M` to a
-- statement:
--   A matrix with entries bounded by `B` maps a vector with small support and sup norm `M` to a
--   vector with entries bounded by `B * |supp v| * M`.
--
--   ```lean
--   theorem MatrixUncertainty.norm_mulVec_le(T : Matrix n n ℂ) (B M : ℝ) (hB : ∀ i j, ‖T i j‖ ≤ B)
--       (hBpos : 0 ≤ B) (v : n → ℂ) (hM : ∀ j, ‖v j‖ ≤ M) (i : n) :
--       ‖T.mulVec v i‖ ≤ B * (vsupport v).card * M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MatrixUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MatrixUncertainty.lean#L43

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



omit [DecidableEq n] in

theorem MatrixUncertainty.norm_mulVec_le(T : Matrix n n ℂ) (B M : ℝ) (hB : ∀ i j, ‖T i j‖ ≤ B)
    (hBpos : 0 ≤ B) (v : n → ℂ) (hM : ∀ j, ‖v j‖ ≤ M) (i : n) :
    ‖T.mulVec v i‖ ≤ B * (vsupport v).card * M := by sorry
