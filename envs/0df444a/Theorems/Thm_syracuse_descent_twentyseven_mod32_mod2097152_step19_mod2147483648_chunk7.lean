-- Prove2me | Theorems.Thm_syracuse_descent_twentyseven_mod32_mod2097152_step19_mod2147483648_chunk7
-- name    : syracuse_descent_twentyseven_mod32_mod2097152_step19_mod2147483648_chunk7
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T17:59:50.127305+00:00
-- url     : https://prove2.me/theorems/fb4f6fff-4db6-4aa1-98ae-b7aebf73d3b9
-- title:
--   Uniform 19-step Syracuse descent, chunk 7 of 10 modulo $2^{31}$
-- statement:
--   For every natural number $n$ whose residue modulo $2^{31}$ lies in the list `syrStep19Chunk7`, the Syracuse map descends in 19 accelerated steps: $$T^{19}(n) < n .$$ The class certificate replays 18 exact rows and a truncated terminal row inside the budget $31$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; the accelerated (Syracuse) map T(n) = (3n+1)/2^v2(3n+1) of the Collatz descent programme on the Collatz Conjecture mission; row certificate architecture of CollatzFrontier.syracuse_terminal_budget_of_descent

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syrStep19Chunk7
set_option maxRecDepth 16384

theorem syracuse_descent_twentyseven_mod32_mod2097152_step19_mod2147483648_chunk7 (n : ℕ)
    (h : n % 2147483648 ∈ syrStep19Chunk7) :
    syracuseStep^[19] n < n := by sorry
