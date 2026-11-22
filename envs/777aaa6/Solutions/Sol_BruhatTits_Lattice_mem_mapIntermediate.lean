-- Prove2me | solution 1 for BruhatTits.Lattice.mem_mapIntermediate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:58:18.720258+00:00
-- url     : https://prove2.me/submissions/8cabba21-133f-4ba1-a288-1d6909ce1474

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
namespace BruhatTits
namespace Lattice
theorem _root_.solution (L M : BruhatTits.Lattice R) (x : L.quotient) :
    x ∈ L.mapIntermediate M ↔ ∃ y : L.M, y.val ∈ M.M ∧ x = L.toQuotient y := by
  change x ∈ Submodule.map L.toQuotient (Submodule.comap L.M.subtype M.M) ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h.symm⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, h.symm⟩
end Lattice
end BruhatTits
