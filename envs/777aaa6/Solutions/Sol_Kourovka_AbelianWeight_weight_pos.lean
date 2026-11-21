-- Prove2me | solution 1 for Kourovka.AbelianWeight.weight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:16.646471+00:00
-- url     : https://prove2.me/submissions/41f6a62c-871b-45b9-9c8c-88760091586c

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_AbelianWeight

set_option autoImplicit true
open Kourovka
open Kourovka.AbelianWeight
variable (M N : Type*) [AddCommGroup M] [AddCommGroup N]
namespace Kourovka.AbelianWeight
theorem _root_.solution [Module.Finite ℤ M] [Nontrivial M] : 0 < weight M := by
  have hc : 0 < Nat.card (Submodule.torsion ℤ M) := Nat.card_pos
  by_cases hr : Module.finrank ℤ M = 0
  · have ht : Module.IsTorsion ℤ M := (Module.finrank_eq_zero_iff_isTorsion (R := ℤ) (M := M)).mp hr
    have hs : Function.Surjective ((Submodule.torsion ℤ M).subtype) := by
      intro x
      exact ⟨⟨x, @ht x⟩, rfl⟩
    letI : Nontrivial (Submodule.torsion ℤ M) := hs.nontrivial
    have hcard : 1 < Nat.card (Submodule.torsion ℤ M) := Finite.one_lt_card
    unfold weight
    omega
  · unfold weight
    omega
end Kourovka.AbelianWeight
