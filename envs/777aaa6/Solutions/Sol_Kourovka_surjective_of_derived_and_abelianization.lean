-- Prove2me | solution 1 for Kourovka.surjective_of_derived_and_abelianization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:19.85484+00:00
-- url     : https://prove2.me/submissions/dd27d5d5-f1d6-4224-aa90-9e585942aaf4

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction

set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]
namespace Kourovka
theorem _root_.solution (f : G →* G)
    (hder : ∀ y ∈ commutator G, ∃ x ∈ commutator G, f x = y)
    (hab : Function.Surjective (Abelianization.map f)) : Function.Surjective f := by
  intro y
  obtain ⟨z, hz⟩ := hab (Abelianization.of y)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  change Abelianization.of (f x) = Abelianization.of y at hz
  have hmem : y * (f x)⁻¹ ∈ commutator G := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hz, mul_inv_cancel]
  obtain ⟨w, _, hw⟩ := hder _ hmem
  exact ⟨w * x, by simp [hw]⟩
end Kourovka
