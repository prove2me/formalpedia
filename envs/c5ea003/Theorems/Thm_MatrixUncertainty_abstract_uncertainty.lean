-- Prove2me | Theorems.Thm_MatrixUncertainty_abstract_uncertainty
-- name    : MatrixUncertainty.abstract_uncertainty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:56:05.002116+00:00
-- url     : https://prove2.me/theorems/f600677a-3286-4e7e-835b-233b34def007
-- title:
--   Abstract uncertainty principle.
-- statement:
--   **Abstract uncertainty principle.** For an invertible transform `T` with inverse `T'`, whose
--   entries are bounded by `B` and `C` respectively, no nonzero vector can be concentrated
--   simultaneously in the source and target coordinates:
--   `1 ≤ B * C * |supp v| * |supp (T v)|`.
--
--   This isolates the structure that the previous cycle showed to be missing: contravariance alone
--   gives nothing, but a *nondegenerate bounded pairing* gives a genuine uncertainty bound.
--
--   ```lean
--   theorem MatrixUncertainty.abstract_uncertainty(T T' : Matrix n n ℂ) (hinv : T' * T = 1)
--       (B C : ℝ) (hB : ∀ i j, ‖T i j‖ ≤ B) (hC : ∀ i j, ‖T' i j‖ ≤ C)
--       (v : n → ℂ) (hv : v ≠ 0) :
--       1 ≤ B * C * ((vsupport v).card * (vsupport (T.mulVec v)).card) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MatrixUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MatrixUncertainty.lean#L68

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

theorem MatrixUncertainty.abstract_uncertainty(T T' : Matrix n n ℂ) (hinv : T' * T = 1)
    (B C : ℝ) (hB : ∀ i j, ‖T i j‖ ≤ B) (hC : ∀ i j, ‖T' i j‖ ≤ C)
    (v : n → ℂ) (hv : v ≠ 0) :
    1 ≤ B * C * ((vsupport v).card * (vsupport (T.mulVec v)).card) := by sorry
