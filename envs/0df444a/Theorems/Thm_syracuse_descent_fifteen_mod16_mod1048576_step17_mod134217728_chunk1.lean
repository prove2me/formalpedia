-- Prove2me | Theorems.Thm_syracuse_descent_fifteen_mod16_mod1048576_step17_mod134217728_chunk1
-- name    : syracuse_descent_fifteen_mod16_mod1048576_step17_mod134217728_chunk1
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T18:35:46.096606+00:00
-- url     : https://prove2.me/theorems/827f686d-5215-4ace-af45-d524c5a4d715
-- title:
--   Uniform 17-step Syracuse descent, chunk 1 of 10 modulo $2^{27}$
-- statement:
--   For every natural number $n$ whose residue modulo $2^{27}$ lies in the list `syrFifteenStep17Chunk1`, the Syracuse map descends in 17 accelerated steps: $$T^{17}(n) < n .$$ The class certificate replays 16 exact rows and a truncated terminal row inside the budget $27$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; the accelerated (Syracuse) map T(n) = (3n+1)/2^v2(3n+1) of the Collatz descent programme on the Collatz Conjecture mission; row certificate architecture of CollatzFrontier.syracuse_terminal_budget_of_descent

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syrFifteenStep17Chunk1
set_option maxRecDepth 16384

theorem syracuse_descent_fifteen_mod16_mod1048576_step17_mod134217728_chunk1 (n : ℕ)
    (h : n % 134217728 ∈ syrFifteenStep17Chunk1) :
    syracuseStep^[17] n < n := by sorry
