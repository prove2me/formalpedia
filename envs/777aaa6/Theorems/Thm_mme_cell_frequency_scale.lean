-- Prove2me | Theorems.Thm_mme_cell_frequency_scale
-- name    : mme_cell_frequency_scale
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:32:52.828336+00:00
-- url     : https://prove2.me/theorems/bf756484-21f8-4571-a161-5ff21c6c4baf
-- title:
--   Positive integer replication preserves child frequencies
-- statement:
--   Let $\mu(c,w)$ be finite nonnegative integer word counts in each cell, and let $k>0$ be an integer. Multiplying every count by $k$ preserves each normalized frequency:
--   $$\frac{k\mu(c,w)}{\sum_v k\mu(c,v)}=\frac{\mu(c,w)}{\sum_v\mu(c,v)}.$$
--   Zero-mass cells are included under the convention that division by zero gives zero.
-- source:
--   Integer replication of regional profiles and the released owner-zero (1,1,6) component.

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

theorem mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by sorry
