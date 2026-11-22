-- Prove2me | Theorems.Thm_Basis_unipotent_pow_irred_mul_eq
-- name    : Basis.unipotent_pow_irred_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:39:08.420762+00:00
-- url     : https://prove2.me/theorems/b8c245f7-e7fb-4f6d-b68b-e25c523e69a5
-- title:
--   Basis: unipotent pow irred mul eq
-- statement:
--   The Basis construction uses the unipotent pow irred mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L130-L134
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Transvect.lean#L130-L134

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Definitions.Def_BruhatTits_Lattice_Transvect
set_option autoImplicit false
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

theorem Basis.unipotent_pow_irred_mul_eq (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (n : ℕ)
    {ϖ : R} (hϖ : Irreducible ϖ) :
    b.unipotent (ϖ ^ n * x) = (b.ntwist₂ hϖ n 0).unipotent x := by sorry
