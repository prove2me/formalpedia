-- Prove2me | Theorems.Thm_syracuse_descent_twentyseven_mod32_mod2097152_step18_mod536870912_chunk5
-- name    : syracuse_descent_twentyseven_mod32_mod2097152_step18_mod536870912_chunk5
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T16:27:52.695078+00:00
-- url     : https://prove2.me/theorems/99a45a12-ffbe-4b13-addf-9ed50693cd4d
-- title:
--   Uniform 18-step Syracuse descent, chunk 5 of 13 modulo $2^{29}$
-- statement:
--   For every natural number $n$ whose residue modulo $2^{29}$ lies in the list `syrStep18Chunk5`, the Syracuse map descends in 18 accelerated steps: $$T^{18}(n) < n .$$ The class certificate replays 17 exact rows and a truncated terminal row inside the budget $29$.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; the accelerated (Syracuse) map T(n) = (3n+1)/2^v2(3n+1) of the Collatz descent programme on the Collatz Conjecture mission; row certificate architecture of CollatzFrontier.syracuse_terminal_budget_of_descent

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syrStep18Chunk5
set_option maxRecDepth 16384

theorem syracuse_descent_twentyseven_mod32_mod2097152_step18_mod536870912_chunk5 (n : ℕ)
    (h : n % 536870912 ∈ syrStep18Chunk5) :
    syracuseStep^[18] n < n := by sorry
