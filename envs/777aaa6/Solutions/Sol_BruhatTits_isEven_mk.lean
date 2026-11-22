-- Prove2me | solution 1 for BruhatTits.isEven_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:23:44.229447+00:00
-- url     : https://prove2.me/submissions/fd7284a6-9814-4ab4-a8e7-e5d879c69ea8

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation

set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (L : BruhatTits.Lattice R) : IsEven ⟦L⟧ ↔ L.IsEven := .rfl
end BruhatTits
