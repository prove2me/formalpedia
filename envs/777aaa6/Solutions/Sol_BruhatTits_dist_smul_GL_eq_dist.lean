-- Prove2me | solution 1 for BruhatTits.dist_smul_GL_eq_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:14:22.915188+00:00
-- url     : https://prove2.me/submissions/cfebc193-78ce-4a67-959a-b5853589367f

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
import Theorems.Thm_P2M_BruhatTits_exists_repr_dist__6b27e91d9e3c
import Theorems.Thm_BruhatTits_dist_twist
import Theorems.Thm_Basis_smulGL_toLattice
import Theorems.Thm_Basis_smulGL_twist


set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise
namespace BruhatTits
theorem _root_.solution (M L : BruhatTits.Lattice R) (g : GL (Fin 2) K) :
    dist (g • M) (g • L) = dist M L := by
  obtain ⟨ϖ, hϖ, b, f, hf, rfl, rfl, hdiff⟩ := exists_repr_dist' M L
  rw [← Basis.smulGL_toLattice, ← Basis.smulGL_toLattice, Basis.smulGL_twist]
  rw [← Nat.cast_inj (R := ℤ), dist_twist _ _ hf, dist_twist _ _ hf]
end BruhatTits
