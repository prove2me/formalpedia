-- Prove2me | Theorems.Thm_mme_CW_2376_supported_two_modes_determine_address
-- name    : mme_CW_2376_supported_two_modes_determine_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:50:54.608016+00:00
-- url     : https://prove2.me/theorems/0adbf769-6d27-4797-8648-72e732c26cfc
-- title:
--   Two modes determine a supported CW square address
-- statement:
--   Let $a$ and $b$ be two length-$N$ addresses in the five-grading of the squared Coppersmith--Winograd tensor, each supported coordinatewise by $I_j+J_j+K_j=4$. If $a$ and $b$ agree as words in any two distinct tensor modes, then they agree in the third mode and hence $a=b$. Equivalently, two distinct supported hyperedges can share at most one mode vertex.
--
--   This is the linearity property needed in the Salem--Spencer collision deletion on journal pp. 267--269: it prevents a collision pair from being counted in two different modes and makes the pruning potential sound.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), squared-tensor support grades and the usual pruning on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_profile_induced_family

open MME

theorem mme_CW_2376_supported_two_modes_determine_address
    {m : ℕ} {a b : CW2376ProfileAddress m}
    (ha : CW2376CoordinatewiseSupported a)
    (hb : CW2376CoordinatewiseSupported b)
    {i k : Fin 3} (hik : i ≠ k)
    (hi : a i = b i) (hk : a k = b k) :
    a = b := by
  sorry
