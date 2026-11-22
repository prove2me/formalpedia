-- Prove2me | solution 1 for BruhatTits.exists_repr_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:55:21.498637+00:00
-- url     : https://prove2.me/submissions/e62117be-9702-4033-8ae4-135a41ed82aa

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
import Theorems.Thm_BruhatTits_eq_dist_iff

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits
namespace BruhatTits
theorem _root_.solution (M L : BruhatTits.Lattice R) :
    ∃ (ϖ : R) (bM : Basis (Fin 2) R M.M) (bL : Basis (Fin 2) R L.M) (f : Fin 2 → ℤ),
      Irreducible ϖ ∧ Antitone f ∧
        (∀ i, (bL i).val = (ϖ ^ f i : K) • (bM i).val) ∧ f 0 - f 1 = dist M L := by
  set n := dist M L with hn
  exact (eq_dist_iff M L n).mp hn.symm
end BruhatTits
