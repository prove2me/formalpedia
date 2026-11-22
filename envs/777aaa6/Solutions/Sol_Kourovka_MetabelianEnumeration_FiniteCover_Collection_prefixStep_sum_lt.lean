-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.prefixStep_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:02.144096+00:00
-- url     : https://prove2.me/submissions/892182d2-b136-43d9-80c3-4506b79547ab

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_prefixStep_sum_bound

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (v : Lattice k) (j : Fin k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hsmall : ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k) :
    (∑ i, |(prefixStep reverse v j i : ℝ)|) < ρ - ρ / (2 * k) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have h := prefixStep_sum_bound hk reverse v j ρ hρ0 hsmall
  have hh : 1 < ρ / (2 * k) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
  have he : ((k : ℝ) - 1) * (ρ / k) + 1 = ρ - 2 * (ρ / (2 * k)) + 1 := by
    field_simp

  rw [he] at h
  linarith
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
