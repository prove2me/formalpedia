-- Prove2me | solution 1 for Kourovka.AbelianWeight.weight_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:50.331311+00:00
-- url     : https://prove2.me/submissions/706a3610-999c-498f-b8c3-9263ad4b080b

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
theorem _root_.solution (e : M ≃+ N) : weight M = weight N := by
  unfold weight
  rw [e.toIntLinearEquiv.finrank_eq, Nat.card_congr (torsionCongr M N e)]
end Kourovka.AbelianWeight
