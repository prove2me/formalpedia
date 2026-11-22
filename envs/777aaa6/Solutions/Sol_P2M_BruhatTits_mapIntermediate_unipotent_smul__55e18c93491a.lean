-- Prove2me | solution 1 for P2M_BruhatTits_mapIntermediate_unipotent_smul__55e18c93491a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:11:07.69017+00:00
-- url     : https://prove2.me/submissions/894e2757-800d-4a07-8770-f17efca716eb

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
import Theorems.Thm_BruhatTits_mapIntermediate_unipotent_smul
import Theorems.Thm_Basis_unipotent_pow_irred_mul_eq


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
namespace BruhatTits
theorem _root_.solution (b : Basis (Fin 2) K (Fin 2 → K)) (x : R)
    (M : BruhatTits.Lattice R) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    ((b.ntwist₂ hϖ n 0).toLattice (R := R)).mapIntermediate (b.unipotent (ϖ ^ n * x) • M) =
      (((b.ntwist₂ hϖ n 0).toLattice (R := R)).mapIntermediate M).map
        ((b.ntwist₂ hϖ n 0).unipotentResidue x).toLinearMap := by
  rw [Basis.unipotent_pow_irred_mul_eq (hϖ := hϖ)]
  apply mapIntermediate_unipotent_smul
end BruhatTits
