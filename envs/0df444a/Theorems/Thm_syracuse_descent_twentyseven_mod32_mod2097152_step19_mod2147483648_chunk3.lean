-- Prove2me | Theorems.Thm_syracuse_descent_twentyseven_mod32_mod2097152_step19_mod2147483648_chunk3
-- name    : syracuse_descent_twentyseven_mod32_mod2097152_step19_mod2147483648_chunk3
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T17:59:48.875893+00:00
-- url     : https://prove2.me/theorems/15615e37-25b2-4c9f-af34-8f8eda4b1df1
-- title:
--   Uniform 19-step Syracuse descent, chunk 3 of 10 modulo $2^{31}$
-- statement:
--   For every natural number $n$ whose residue modulo $2^{31}$ lies in the list `syrStep19Chunk3`, the Syracuse map descends in 19 accelerated steps: $$T^{19}(n) < n .$$ The class certificate replays 18 exact rows and a truncated terminal row inside the budget $31$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; the accelerated (Syracuse) map T(n) = (3n+1)/2^v2(3n+1) of the Collatz descent programme on the Collatz Conjecture mission; row certificate architecture of CollatzFrontier.syracuse_terminal_budget_of_descent

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syrStep19Chunk3
set_option maxRecDepth 16384

theorem syracuse_descent_twentyseven_mod32_mod2097152_step19_mod2147483648_chunk3 (n : ℕ)
    (h : n % 2147483648 ∈ syrStep19Chunk3) :
    syracuseStep^[19] n < n := by sorry
