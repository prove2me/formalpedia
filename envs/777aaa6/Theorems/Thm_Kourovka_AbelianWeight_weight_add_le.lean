-- Prove2me | Theorems.Thm_Kourovka_AbelianWeight_weight_add_le
-- name    : Kourovka.AbelianWeight.weight_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:19.900061+00:00
-- url     : https://prove2.me/theorems/a78ed2cf-759e-4cb6-b36e-0361463df29f
-- title:
--   Abelian Weight: weight add le
-- statement:
--   The measure is superadditive under direct products.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/AbelianWeight.lean#L75-L89
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/AbelianWeight.lean#L75-L89

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

theorem Kourovka.AbelianWeight.weight_add_le [Module.Finite ℤ M] [Module.Finite ℤ N] :
    weight M + weight N ≤ weight (M × N) := by sorry
