-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ModuleRealization.map_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:31.744741+00:00
-- url     : https://prove2.me/submissions/20e7012d-6596-4ff7-8851-5b0801dd4470

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization

set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]
namespace Kourovka.MetabelianEnumeration.ModuleRealization
theorem _root_.solution (j : Multiplicative M →* G) (xs : List M) :
    j (Multiplicative.ofAdd xs.sum) = (xs.map fun m => j (Multiplicative.ofAdd m)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa using congrArg (fun g => j (Multiplicative.ofAdd x) * g) ih
end Kourovka.MetabelianEnumeration.ModuleRealization
