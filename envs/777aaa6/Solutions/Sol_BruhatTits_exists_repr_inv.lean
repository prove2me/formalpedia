-- Prove2me | solution 1 for BruhatTits.exists_repr_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:13:16.158169+00:00
-- url     : https://prove2.me/submissions/aa7a0043-50b0-416b-90cc-b1f731667445

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
import Theorems.Thm_BruhatTits_exists_repr_inv_of_fixed

set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise
namespace BruhatTits
theorem _root_.solution (x y : Vertices R) :
    ∃ (ϖ : R) (_ : Irreducible ϖ) (M L : BruhatTits.Lattice R)
      (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M),
      ⟦M⟧ = x ∧ ⟦L⟧ = y ∧ bL 0 = ϖ ^ (inv x y) • (bM 0).val ∧ bL 1 = (bM 1).val := by
  refine Quotient.inductionOn' x (fun M ↦ ?_)
  obtain ⟨ϖ, hϖ, L, bM, bL, hL, hbL₀, hbL₁⟩ := exists_repr_inv_of_fixed M y
  use ϖ, hϖ, M, L, bM, bL
end BruhatTits
