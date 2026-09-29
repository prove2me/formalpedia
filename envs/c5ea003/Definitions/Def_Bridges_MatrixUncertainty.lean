-- Prove2me | Definitions.Def_Bridges_MatrixUncertainty
-- name    : Bridges_MatrixUncertainty
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:15.170758+00:00
-- url     : https://prove2.me/theorems/7b80628e-e78a-4abb-93ce-b541e74aa03a
-- title:
--   Aether Catalog definitions — Bridges_MatrixUncertainty
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.MatrixUncertainty`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/MatrixUncertainty.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty

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

namespace MatrixUncertainty

section Abstract

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Classical in
/-- The support of a coordinate vector, as a finite set. -/
noncomputable def vsupport (v : n → ℂ) : Finset n := Finset.univ.filter fun j => v j ≠ 0




end Abstract

/-! ## The Fourier transform as an instance of the abstract principle -/

section Fourier

variable {N : ℕ} [NeZero N]

/-- The Fourier matrix of `ZMod N`. -/
noncomputable def dftMatrix (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun k j => stdAddChar (-(j * k))

/-- The inverse Fourier matrix of `ZMod N`. -/
noncomputable def invDftMatrix (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun k j => (N : ℂ)⁻¹ * stdAddChar (j * k)







end Fourier

/-! ## Boundedness is essential

The abstract principle uses two hypotheses. Invertibility alone is not enough: the identity
matrix is invertible with `B = C = 1`, but the bound it produces, `1 ≤ |supp v| * |supp v|`, is
vacuous. Concretely, an invertible transform can map a delta to a delta, so no uncertainty bound
better than `1` can follow from invertibility alone; the gain in the Fourier case comes entirely
from the smallness `C = 1/N` of the inverse entries. -/

section Necessity


end Necessity

end MatrixUncertainty


