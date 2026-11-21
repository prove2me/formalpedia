-- Prove2me | Theorems.Thm_Kourovka_AbelianWeight_finrank_add_le
-- name    : Kourovka.AbelianWeight.finrank_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:59.127034+00:00
-- url     : https://prove2.me/theorems/62fbdb23-334a-4a31-8841-36df0b5eb91b
-- title:
--   Abelian Weight: finrank add le
-- statement:
--   The Abelian Weight construction uses the finrank add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/AbelianWeight.lean#L67-L72
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/AbelianWeight.lean#L67-L72

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

theorem Kourovka.AbelianWeight.finrank_add_le [Module.Finite ℤ M] [Module.Finite ℤ N] :
    Module.finrank ℤ M + Module.finrank ℤ N ≤ Module.finrank ℤ (M × N) := by sorry
