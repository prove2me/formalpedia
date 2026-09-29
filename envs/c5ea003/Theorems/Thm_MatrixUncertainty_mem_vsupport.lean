-- Prove2me | Theorems.Thm_MatrixUncertainty_mem_vsupport
-- name    : MatrixUncertainty.mem_vsupport
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:02:54.983794+00:00
-- url     : https://prove2.me/theorems/0fa16644-e2ef-4dd7-8ef5-cfa01b155c6d
-- title:
--   Mem vsupport
-- statement:
--   Formal statement of `MatrixUncertainty.mem_vsupport` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem MatrixUncertainty.mem_vsupport{v : n → ℂ} {j : n} : j ∈ vsupport v ↔ v j ≠ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MatrixUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MatrixUncertainty.lean#L38

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


open scoped Classical in
omit [DecidableEq n] in
@[simp]

theorem MatrixUncertainty.mem_vsupport{v : n → ℂ} {j : n} : j ∈ vsupport v ↔ v j ≠ 0 := by sorry
