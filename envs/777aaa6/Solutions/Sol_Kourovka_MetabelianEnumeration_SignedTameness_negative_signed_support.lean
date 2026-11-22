-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.SignedTameness.negative_signed_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:22.532658+00:00
-- url     : https://prove2.me/submissions/a93a4d12-aa0b-4ad9-b866-9afb0a2f2b75

import Definitions.Def_Kourovka_Modules_ValuationModule
import Definitions.Def_Kourovka_Modules_SignedTameness

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.SignedTameness
open FiniteCover ConeVerifier ValuationModule TamenessCompactness
variable {k : ℕ} {M : Type*} [AddCommGroup M] [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.SignedTameness
theorem _root_.solution {x : Fin k → ℝ} (p : GroupRing (Lattice k))
    (hp : ∀ u ∈ p.support, 0 < (-character x) u) :
    ∀ u ∈ signedSupport (false, p), 0 < dot u x := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  simpa [dot, character, mul_comm, Finset.sum_neg_distrib] using hp v (Finset.mem_toList.mp hv)
end Kourovka.MetabelianEnumeration.SignedTameness
