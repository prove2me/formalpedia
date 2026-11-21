-- Prove2me | Theorems.Thm_Kourovka_diagonalRight_mul_center_surjective
-- name    : Kourovka.diagonalRight_mul_center_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:29.000488+00:00
-- url     : https://prove2.me/theorems/9ab391ca-5b41-4948-bcf7-5676ebf8b242
-- title:
--   Kourovka: diagonal Right mul center surjective
-- statement:
--   The Kourovka construction uses the diagonal Right mul center surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L29-L38
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L29-L38

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.diagonalRight_mul_center_surjective (f : A × B →* A × B)
    (hf : Function.Surjective f) (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) :
    ∀ y, ∃ x z, z ∈ Subgroup.center B ∧ diagonalRight f x * z = y := by sorry
