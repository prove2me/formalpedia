-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableClosure.stages_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:01.576179+00:00
-- url     : https://prove2.me/submissions/ed7c2955-2f0c-4663-949e-4332014d88da

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.ComputableClosure
theorem _root_.solution (rels C : List G) (n : ℕ) {x : G}
    (hx : x ∈ stages rels C n) : x ∈ Subgroup.normalClosure {r | r ∈ rels} := by
  induction n generalizing x with
  | zero =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_normalClosure hx
  | succ n ih =>
    rw [stages_succ] at hx
    rcases (mem_expand _ _ _).mp hx with hx | ⟨y, hy, rfl⟩ |
      ⟨y, hy, z, hz, rfl⟩ | ⟨g, _, y, hy, rfl⟩
    · exact ih hx
    · exact Subgroup.inv_mem _ (ih hy)
    · exact Subgroup.mul_mem _ (ih hy) (ih hz)
    · exact Subgroup.Normal.conj_mem inferInstance _ (ih hy) _
end Kourovka.MetabelianEnumeration.ComputableClosure
