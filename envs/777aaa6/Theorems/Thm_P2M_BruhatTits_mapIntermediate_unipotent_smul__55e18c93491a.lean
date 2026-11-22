-- Prove2me | Theorems.Thm_P2M_BruhatTits_mapIntermediate_unipotent_smul__55e18c93491a
-- name    : P2M_BruhatTits_mapIntermediate_unipotent_smul__55e18c93491a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:00:28.675783+00:00
-- url     : https://prove2.me/theorems/1cccda77-3110-4f16-81df-5db176dcb3a3
-- title:
--   P2 M Bruhat Tits map Intermediate unipotent smul  55e18c93491a: P2 M Bruhat Tits map Intermediate unipotent smul  55e18c93491a
-- statement:
--   Variant of `mapIntermediate_unipotent_smul` for the lattice spanned by `(ϖ ^ n • b₀, b₁)`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L544-L550
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L544-L550

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R]
open BruhatTits
set_option synthInstance.maxHeartbeats 30000
open IsLocalRing
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 500000
open Pointwise
variable [IsFractionRing R K]

theorem P2M_BruhatTits_mapIntermediate_unipotent_smul__55e18c93491a (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (M : BruhatTits.Lattice R) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    ((b.ntwist₂ hϖ n 0).toLattice (R := R)).mapIntermediate (b.unipotent (ϖ ^ n * x) • M) =
      (((b.ntwist₂ hϖ n 0).toLattice (R := R)).mapIntermediate M).map
        ((b.ntwist₂ hϖ n 0).unipotentResidue x).toLinearMap := by sorry

alias «BruhatTits».«mapIntermediate_unipotent_smul'» := P2M_BruhatTits_mapIntermediate_unipotent_smul__55e18c93491a
