-- Prove2me | Theorems.Thm_XMX_nonstationary_inventory_fat_bound
-- name    : XMX.nonstationary_inventory_fat_bound
-- status  : Proved
-- author  : @visuddhi
-- created : 2026-10-08T17:02:44.224387+00:00
-- url     : https://prove2.me/theorems/169d31fe-a5f0-43c4-8355-b79cca41ae05
-- title:
--   Xie–Ma–Xin Theorem 4.9: normalized inventory fat-shattering bound
-- statement:
--   For every positive T,U, nonnegative integer lead time L, period k<T, and margin 0<gamma<=1, every gamma-shattered sample for the normalized inventory class has size m<=2/gamma+1. Shattering uses >tau+gamma for high labels and <=tau-gamma for low labels. This concerns the inventory class, not its loss pseudodimension.
-- source:
--   Yaqi Xie, Will Ma, Linwei Xin, VC Theory for Inventory Policies, arXiv:2404.11509v3 (2026-02-01), Theorem 4.9 and Section 8.5

import Definitions.Def_XMX_NonstationaryInventory
import Definitions.Def_XMX_CyclicPartition

set_option autoImplicit false
open MeasureTheory

namespace XMX

theorem nonstationary_inventory_fat_bound
    (T L : ℕ) (hT : 0 < T) (U γ : ℝ) (hU : 0 < U)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (k : ℕ) (hk : k < T)
    (m : ℕ) (x : Fin m → Demand T L U) (τ : Fin m → ℝ)
    (hshatter : Shatters (normalizedInventory T L U k) γ m x τ) :
    (m : ℝ) ≤ 2 / γ + 1 := by sorry

end XMX
