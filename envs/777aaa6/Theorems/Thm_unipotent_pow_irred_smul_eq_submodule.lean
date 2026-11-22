-- Prove2me | Theorems.Thm_unipotent_pow_irred_smul_eq_submodule
-- name    : unipotent_pow_irred_smul_eq_submodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:38:27.669181+00:00
-- url     : https://prove2.me/theorems/4a77fc28-aa67-4c97-b496-a36b003c19ad
-- title:
--   unipotent pow irred smul eq submodule: unipotent pow irred smul eq submodule
-- statement:
--   If `b = (b₀, b₁)` is a basis of `K^2`, then the submodule spanned by `(ϖ ^ k • b₀, b₁)`
--   is invariant under the action of `b.unipotent (ϖ ^ n * x)` if `n ≥ k`.
--
--   This is used in `Lattice.exists_GL_forall_smul_eq_ntwist₂_of_isSimpleChain_cons`: We use
--   such unipotent matrices to inductively bring a simple chain of lattices in standard form. This
--   makes sure that in the `n + 1`th step, multiplying with a unipotent matrix does not change
--   the first `n` terms of the chain.
--
--   See `unipotent_pow_irred_smul_eq` for a version for `Basis.toLattice`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L147-L212
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L147-L212

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

theorem unipotent_pow_irred_smul_eq_submodule {ϖ : R} (hϖ : Irreducible ϖ)
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (k n : ℕ) (hkn : k ≤ n) :
    b.unipotent (ϖ ^ n * x) • (b.ntwist₂ hϖ k 0).toSubmodule (R := R) =
      (b.ntwist₂ hϖ k 0).toSubmodule := by sorry
