-- Prove2me | Theorems.Thm_syracuse_descent_fifteen_mod16_mod1048576_step15_mod16777216_chunk13
-- name    : syracuse_descent_fifteen_mod16_mod1048576_step15_mod16777216_chunk13
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-23T11:26:34.152906+00:00
-- url     : https://prove2.me/theorems/9ada058a-0d27-4fb0-a3b0-f4c032db95e8
-- title:
--   Fourteen-row Syracuse descent on chunk 13 of the modulus-$2^{24}$ refinement (2361 residue classes)
-- statement:
--   Let $T(n)$ be the odd part of $3n+1$ (the platform's Syracuse map `syracuseStep`), and let $T^{15}$ denote fifteen successive applications. Let $R_{13}$ be the explicit list of 2361 distinct residues modulo $2^{24} = 16777216$ held in the platform definition `syrFifteenStep15Chunk13`. For every natural number $n$,
--
--   $$
--   n \bmod 16777216 \in R_{13} \quad \Longrightarrow \quad T^{15}(n) < n .
--   $$
--
--   This is chunk 13 of 16 of the modulus-$2^{24}$ refinement of the fifteen-branch residual after the step-14 refinement; the sixteen chunks are disjoint and together certify 37768 residue classes modulo $2^{24}$, each carrying a descent certificate with exponent budget $24$. This advances milestone *Open frontier — Residual 15 mod 16 classes*.
--
--   **Method.** For each $r \in R_{13}$ the first fourteen rows $3 b_k + 1 = 2^{a_k} b_{k+1}$ are replayed exactly with odd intermediate quotients, and the fifteenth row is truncated to the remaining exponent budget; the certificate is accepted exactly when the truncated quotient lies below $r$. The chunk theorem is one kernel evaluation of that checker over the 2361-element literal, and the descent on the whole residue class follows from the published terminal-budget theorem of the front.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syrFifteenStep15Chunk13
set_option maxRecDepth 16384

theorem syracuse_descent_fifteen_mod16_mod1048576_step15_mod16777216_chunk13 (n : ℕ)
    (h : n % 16777216 ∈ syrFifteenStep15Chunk13) :
    syracuseStep^[15] n < n := by sorry
