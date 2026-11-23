-- Prove2me | Theorems.Thm_syracuse_descent_fifteen_mod16_mod1048576_step17_mod134217728_chunk4
-- name    : syracuse_descent_fifteen_mod16_mod1048576_step17_mod134217728_chunk4
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T18:35:52.6449+00:00
-- url     : https://prove2.me/theorems/009e82e5-6204-4f46-b6fe-8ddd337a200e
-- title:
--   Uniform 17-step Syracuse descent, chunk 4 of 10 modulo $2^{27}$
-- statement:
--   For every natural number $n$ whose residue modulo $2^{27}$ lies in the list `syrFifteenStep17Chunk4`, the Syracuse map descends in 17 accelerated steps: $$T^{17}(n) < n .$$ The class certificate replays 16 exact rows and a truncated terminal row inside the budget $27$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; the accelerated (Syracuse) map T(n) = (3n+1)/2^v2(3n+1) of the Collatz descent programme on the Collatz Conjecture mission; row certificate architecture of CollatzFrontier.syracuse_terminal_budget_of_descent

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syrFifteenStep17Chunk4
set_option maxRecDepth 16384

theorem syracuse_descent_fifteen_mod16_mod1048576_step17_mod134217728_chunk4 (n : ℕ)
    (h : n % 134217728 ∈ syrFifteenStep17Chunk4) :
    syracuseStep^[17] n < n := by sorry
