-- Prove2me | Theorems.Thm_WilliamsonShmoys_unpack_low_cells_arith
-- name    : WilliamsonShmoys.unpack_low_cells_arith
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T11:45:50.417426+00:00
-- url     : https://prove2.me/theorems/d04d17ad-0aa9-47ca-a949-4d182b1781ee
-- title:
--   Recovering the packed cells by division and remainder
-- statement:
--   Let $k\in\mathbb N$ and $b_2,\dots,b_7\in\{0,1\}$, and let $P=64k+32b_2+16b_3+8b_4+4b_5+2b_6+b_7$. Then
--
--   $$\lfloor P/64\rfloor=k,\quad \lfloor (P\bmod 64)/32\rfloor=b_2,\quad\dots,\quad P\bmod 2=b_7.$$
--
--   This is the decoding counterpart of the cell-packing fragment `ram_pack_low_cells`.

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.unpack_low_cells_arith (k b2 b3 b4 b5 b6 b7 : ℕ)
    (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1) (h5 : b5 ≤ 1) (h6 : b6 ≤ 1) (h7 : b7 ≤ 1) :
    let P := 64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7
    P / 64 = k ∧ P % 64 / 32 = b2 ∧ P % 32 / 16 = b3 ∧ P % 16 / 8 = b4 ∧
      P % 8 / 4 = b5 ∧ P % 4 / 2 = b6 ∧ P % 2 = b7 := by sorry
