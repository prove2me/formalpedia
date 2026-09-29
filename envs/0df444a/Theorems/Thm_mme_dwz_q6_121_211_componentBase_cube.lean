-- Prove2me | Theorems.Thm_mme_dwz_q6_121_211_componentBase_cube
-- name    : mme_dwz_q6_121_211_componentBase_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:16:56.712609+00:00
-- url     : https://prove2.me/theorems/a0c596e0-09dc-4fcf-8e00-954ec30699ce
-- title:
--   Exact cube of the Table-2 $121/211$ component base
-- statement:
--   For the $q=6$ rotated coupled constituents $(1,2,1)$ and $(2,1,1)$, Duan--Wu--Zhou use the common Table-2 base
--
--   $$
--   B(\tau)=2^{2/3}6^{\tau}\bigl(6^{3\tau}+2\bigr)^{1/3}.
--   $$
--
--   Its cube is exactly
--
--   $$
--   B(\tau)^3=4\,6^{3\tau}\bigl(6^{3\tau}+2\bigr).
--   $$
--
--   This identity converts the Section 6.3 component formula into the raw cyclic tau-value base of the coupled Coppersmith--Winograd tensor without numerical approximation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Lemma 4.6(d) and Section 6.3/Table 2 component values, PDF pp. 32-33 and 59-60; https://arxiv.org/abs/2210.10173.

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data

open MME.DWZSquare

set_option autoImplicit false

theorem mme_dwz_q6_121_211_componentBase_cube (tau : ℝ) :
    componentBase tau (13 : Fin 15) ^ (3 : ℕ) =
      4 * Real.rpow 6 (3 * tau) *
        (Real.rpow 6 (3 * tau) + 2) := by sorry
