-- Prove2me | Theorems.Thm_syracuse_descent_fifteen_mod16_mod1048576_step16_mod67108864_chunk1
-- name    : syracuse_descent_fifteen_mod16_mod1048576_step16_mod67108864_chunk1
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T12:34:14.010499+00:00
-- url     : https://prove2.me/theorems/ba45481a-c505-4e2e-8317-fa3970d5f66c
-- title:
--   Sixteen-step Syracuse descent on chunk 1 of the modulus-$2^{26}$ refinement (2400 residue classes)
-- statement:
--   Let $T(n)$ be the odd part of $3n+1$ (the platform's Syracuse map `syracuseStep`), and let $T^{16}$ denote sixteen successive applications. Let $R_1$ be the explicit list of 2400 distinct residues modulo $2^{26}=67108864$ enumerated in the definition `syrFifteenStep16Chunk1`. For every natural number $n$,
--
--   $$
--   n\bmod 67108864\in R_{1}\quad\Longrightarrow\quad T^{16}(n)<n.
--   $$
--
--   This is chunk 1 of 32 of the modulus-$2^{26}$ refinement of the [fifteen-branch residual after the modulus-$2^{24}$ refinement](https://prove2.me/theorems/1184f116-9bfe-49df-bda5-041ca8c276cb). The certificate replays fifteen exact rows `3 b_i + 1 = 2 ^ a_i b_(i+1)` from the residue and closes with a truncated terminal row inside the budget $S_{15} + e \le 26$, landing strictly below the starting residue; the Proved theorem `CollatzFrontier.syracuse_terminal_budget_of_descent` turns that package into the strict inequality above.
-- source:
--   Original computation of this contribution (explicit certified refinement of https://prove2.me/theorems/1184f116-9bfe-49df-bda5-041ca8c276cb from modulus 2^24 to 2^26, split into 32 kernel-checked chunks; the residue table is computed, not quoted from the literature). Method: residue-class descent via the Proved theorem CollatzFrontier.syracuse_terminal_budget_of_descent, https://prove2.me/theorems/2513a4d3-77eb-4b93-9876-33755812122c; exact Syracuse definition https://prove2.me/theorems/2d5fcb43-85b2-4d75-beb8-3e236e66eac3.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syrFifteenStep16Chunk1
set_option maxRecDepth 16384

theorem syracuse_descent_fifteen_mod16_mod1048576_step16_mod67108864_chunk1 (n : ℕ)
    (h : n % 67108864 ∈ syrFifteenStep16Chunk1) :
    syracuseStep^[16] n < n := by sorry
