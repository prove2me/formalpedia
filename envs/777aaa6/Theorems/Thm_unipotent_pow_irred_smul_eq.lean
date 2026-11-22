-- Prove2me | Theorems.Thm_unipotent_pow_irred_smul_eq
-- name    : unipotent_pow_irred_smul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:39:07.778761+00:00
-- url     : https://prove2.me/theorems/b9d1aa2a-c7a2-45e9-a057-c41bcc83d9dd
-- title:
--   unipotent pow irred smul eq: unipotent pow irred smul eq
-- statement:
--   Version of `unipotent_pow_irred_smul_eq_submodule` for `Basis.toLattice`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L215-L221
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L215-L221

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

theorem unipotent_pow_irred_smul_eq {ϖ : R} (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K))
    (x : R) (k n : ℕ) (hkn : k ≤ n) :
    b.unipotent (ϖ ^ n * x) • (b.ntwist₂ hϖ k 0).toLattice (R := R) =
      (b.ntwist₂ hϖ k 0).toLattice := by sorry
