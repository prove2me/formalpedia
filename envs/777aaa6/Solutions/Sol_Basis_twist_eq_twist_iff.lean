-- Prove2me | solution 1 for Basis.twist_eq_twist_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:16:54.967025+00:00
-- url     : https://prove2.me/submissions/15002456-e00e-4e5f-b637-1793cb24125d

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_Basis_twist_le_twist_iff

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
open BigOperators
namespace Basis
theorem _root_.solution [Fintype ι] (b : Basis ι K (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) (f g : ι → ℤ) :
    (b.twist hϖ f).toSubmodule (R := R) = (b.twist hϖ g).toSubmodule (R := R) ↔ g = f := by
  constructor
  · intro h
    apply le_antisymm
    rw [← b.twist_le_twist_iff hϖ, h]
    rw [← b.twist_le_twist_iff hϖ, h]
  · intro h
    rw [h]
end Basis
