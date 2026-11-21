-- Prove2me | solution 1 for Kourovka.ProductHom.row_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:41.93627+00:00
-- url     : https://prove2.me/submissions/526151a4-66c6-4aad-b655-3c287c1076b9

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Prod
import Definitions.Def_Kourovka_Components
import Theorems.Thm_Kourovka_ProductHom_decompose

set_option autoImplicit true
open Kourovka
variable {A B K : Type*} [Group A] [Group B] [Group K]
open Kourovka.ProductHom
namespace Kourovka.ProductHom
theorem _root_.solution (f : A × B →* K) (hf : Function.Surjective f) (k : K) :
    ∃ a b, left f a * right f b = k := by
  obtain ⟨⟨a, b⟩, hk⟩ := hf k
  exact ⟨a, b, (decompose f a b).symm.trans hk⟩
end Kourovka.ProductHom
