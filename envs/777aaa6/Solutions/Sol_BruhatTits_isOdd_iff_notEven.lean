-- Prove2me | solution 1 for BruhatTits.isOdd_iff_notEven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:24:05.546242+00:00
-- url     : https://prove2.me/submissions/f7e6dad7-9bbd-4909-b21f-d848a8730d2f

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
theorem _root_.solution (x : Vertices R) : IsOdd x ↔ ¬ IsEven x := by
  induction' x using Quotient.inductionOn with L
  exact L.isOdd_iff_notEven
end BruhatTits
