-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.satisfies_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:20.64304+00:00
-- url     : https://prove2.me/submissions/96cf50cd-089b-4c8e-91a1-7cb3de5c877d

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (n : ℕ) (rows : List RowCode) (x : Fin n → ℝ) :
    FourierMotzkin.Satisfies (rows.map (decodeRow n)) x ↔ Satisfies n rows x := by
  simp only [FourierMotzkin.Satisfies, Satisfies, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
end Kourovka.MetabelianEnumeration.ComputableCone
