-- Prove2me | solution 1 for Kourovka.AbelianWeight.finrank_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:24.055986+00:00
-- url     : https://prove2.me/submissions/2a61c3f9-afd5-46e0-9a67-4215d7d130df

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
theorem _root_.solution [Module.Finite ℤ M] [Module.Finite ℤ N] :
    Module.finrank ℤ M + Module.finrank ℤ N ≤ Module.finrank ℤ (M × N) := by
  have h := lift_rank_add_lift_rank_le_rank_prod ℤ M N
  rw [← Module.finrank_eq_rank ℤ M, ← Module.finrank_eq_rank ℤ N,
    ← Module.finrank_eq_rank ℤ (M × N)] at h
  simpa only [Cardinal.lift_natCast, ← Nat.cast_add, Nat.cast_le] using h
end Kourovka.AbelianWeight
