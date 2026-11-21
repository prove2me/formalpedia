-- Prove2me | solution 1 for Kourovka.product_kernel_le_derived
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:17.200432+00:00
-- url     : https://prove2.me/submissions/dcce09bf-3c20-46bd-a3ed-322f26d3c8cd

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
import Theorems.Thm_Kourovka_ker_le_commutator_of_surjective


set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f) :
    f.ker ≤ (commutator A).prod (commutator B) := by
  have h := ker_le_commutator_of_surjective f hf
  have heq : commutator (A × B) = (commutator A).prod (commutator B) := by
    simpa only [commutator_def, Subgroup.top_prod_top] using
      Subgroup.commutator_prod_prod (⊤ : Subgroup A) ⊤ (⊤ : Subgroup B) ⊤
  exact h.trans_eq heq
end Kourovka
