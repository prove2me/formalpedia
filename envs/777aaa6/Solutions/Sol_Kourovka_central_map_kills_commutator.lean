-- Prove2me | solution 1 for Kourovka.central_map_kills_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:46.32498+00:00
-- url     : https://prove2.me/submissions/cb743153-2e1b-4655-b235-d9a19d487f7b

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components

set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
namespace Kourovka
theorem _root_.solution (f : A →* B)
    (hf : ∀ a, f a ∈ Subgroup.center B) : commutator A ≤ f.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (hf b) (f a))
end Kourovka
