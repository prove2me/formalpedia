-- Prove2me | solution 1 for Kourovka.AbelianWeight.weight_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:59.241511+00:00
-- url     : https://prove2.me/submissions/2dad7515-2651-4e8a-8e9f-862c0da7ef7c

import Definitions.Def_Kourovka_Hopfian
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_AbelianWeight
import Theorems.Thm_Kourovka_AbelianWeight_finrank_add_le

set_option autoImplicit true
open Kourovka
open Kourovka.AbelianWeight
variable (M N : Type*) [AddCommGroup M] [AddCommGroup N]
namespace Kourovka.AbelianWeight
theorem _root_.solution [Module.Finite ℤ M] [Module.Finite ℤ N] :
    weight M + weight N ≤ weight (M × N) := by
  have hM : 0 < Nat.card (Submodule.torsion ℤ M) := Nat.card_pos
  have hN : 0 < Nat.card (Submodule.torsion ℤ N) := Nat.card_pos
  have hr := finrank_add_le M N
  have hc : Nat.card (Submodule.torsion ℤ (M × N)) =
      Nat.card (Submodule.torsion ℤ M) * Nat.card (Submodule.torsion ℤ N) := by
    rw [Nat.card_congr (torsionProdEquiv M N), Nat.card_prod]
  unfold weight
  rw [hc]
  have hp : Nat.card (Submodule.torsion ℤ M) + Nat.card (Submodule.torsion ℤ N) ≤
      Nat.card (Submodule.torsion ℤ M) * Nat.card (Submodule.torsion ℤ N) + 1 := by
    nlinarith [Nat.zero_le ((Nat.card (Submodule.torsion ℤ M) - 1) *
      (Nat.card (Submodule.torsion ℤ N) - 1))]
  omega
end Kourovka.AbelianWeight
