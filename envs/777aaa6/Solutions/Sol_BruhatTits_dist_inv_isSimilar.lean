-- Prove2me | solution 1 for BruhatTits.dist_inv_isSimilar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:04:51.106918+00:00
-- url     : https://prove2.me/submissions/d910868c-2912-420d-bc86-87fa054d5dfc

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
import Theorems.Thm_BruhatTits_dist_symm
import Theorems.Thm_BruhatTits_dist_smul_eq_dist

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
open Pointwise
omit [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
variable [IsDiscreteValuationRing ↥R] [IsFractionRing (↥R) K]
namespace BruhatTits
theorem _root_.solution (M L M' L' : BruhatTits.Lattice R)
    (hM : Lattice.IsSimilar R M M') (hL : Lattice.IsSimilar R L L') : dist M L = dist M' L' := by
  obtain ⟨a, rfl⟩ := hM
  obtain ⟨b, rfl⟩ := hL
  rw [dist_smul_eq_dist]
  nth_rw 2 [dist_symm]
  rw [dist_smul_eq_dist, dist_symm]
end BruhatTits
