-- Prove2me | solution 1 for Couret.STROBO2TORS.allSquareFibres_squareFibre_member
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:10.365372+00:00
-- url     : https://prove2.me/submissions/3d6764a7-f7aa-4cf0-8b14-8efe49d39926

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_preimage
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]









/-- Any member of a genuine complete square fibre determines that fibre. -/
theorem p2m_local_allSquareFibres_squareFibre_member (F : Finset (Finset G))
    (hF : F ∈ (allSquareFibres : Finset (Finset (Finset G))))
    (S : Finset G) (hS : S ∈ F) : squareFibre S = F := by
  have hh := allSquareFibres_preimage F hF
  have h : S ∈ tripleSupports.filter (fun T : Finset G => squareFibre T = F) := by
    rw [hh]
    exact hS
  exact (Finset.mem_filter.mp h).2



























/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (F : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
        (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
      (@Couret.STROBO2TORS.allSquareFibres.{p2m_u_0} G inst inst_1 inst_2) F →
    ∀ (S : Finset.{p2m_u_0} G),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
            (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
          F S →
        @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) F := @_root_.Couret.STROBO2TORS.p2m_local_allSquareFibres_squareFibre_member

