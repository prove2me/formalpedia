-- Prove2me | solution 1 for BruhatTits.smul_isStandardNeighbour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:10:32.113202+00:00
-- url     : https://prove2.me/submissions/2d6b41f4-d5d3-4287-aef0-1efb98dbf924

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
import Theorems.Thm_BruhatTits_scalar_smul_GL_smul
import Theorems.Thm_BruhatTits_smul_lt_iff


set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
namespace BruhatTits
theorem _root_.solution (g : GL (Fin 2) K) (M L : BruhatTits.Lattice R) (h : IsStandardNeighbour M L) :
    IsStandardNeighbour (g • M) (g • L) where
  lt := by
    rw [Lattice.smul_M, Lattice.smul_M, smul_lt_iff]
    exact h.lt
  ϖlt ϖ hϖ := by
    rw [Lattice.smul_M, Lattice.smul_M, Subring.smul_def, scalar_smul_GL_smul, smul_lt_iff]
    exact h.ϖlt ϖ hϖ
end BruhatTits
