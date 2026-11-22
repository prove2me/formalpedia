-- Prove2me | Theorems.Thm_syracuse_descent_twentyseven_mod32_mod2097152_step17_mod134217728_chunk6
-- name    : syracuse_descent_twentyseven_mod32_mod2097152_step17_mod134217728_chunk6
-- status  : Proved
-- author  : @Siyuan Chen
-- created : 2026-11-22T17:25:42.1214+00:00
-- url     : https://prove2.me/theorems/3f63563a-fdd0-4900-9d70-85c4383c2d0f
-- title:
--   Seventeen-step Syracuse descent on chunk 6 of the modulus-$2^{27}$ refinement (2420 residue classes)
-- statement:
--   Let $T(n)$ be the odd part of $3n+1$ (the platform's Syracuse map `syracuseStep`), and let $T^{17}$ denote seventeen successive applications. Let $R_6$ be the explicit list `syrStep17Chunk6` of 2420 residues modulo $2^{27}=134217728$ (a published definition, imported by this statement). For every natural number $n$,
--
--   $$
--   n\bmod 134217728\in R_{6}\quad\Longrightarrow\quad T^{17}(n)<n.
--   $$
--
--   This is chunk 6 of 24 of the modulus-$2^{27}$ refinement of the [twentyseven-branch residual after the modulus-$2^{26}$ refinement](https://prove2.me/theorems/be7d88ec-edf6-4cd4-aef7-5196be4d9650); the chunks are disjoint and together cover 58040 residue classes, all lying over the leaf's 184697 surviving classes modulo $2^{26}$.
--
--   **Method.** For each $r\in R_6$ the first sixteen Syracuse steps of $r$ are exact rows $3b_j+1=2^{a_j}b_{j+1}$ with $b_0=r$ and odd $b_{j+1}$, with $S=\sum_{j<16}a_j\le 27$, and the seventeenth row is closed by a divisor exponent $e=\min(v_2(3b_{16}+1),\,27-S)$ with quotient $B=(3b_{16}+1)/2^{e}<r$. The published theorem [`CollatzFrontier.syracuse_terminal_budget_of_descent`](https://prove2.me/theorems/2513a4d3-77eb-4b93-9876-33755812122c) then gives $T^{17}(r+2^{27}q)<r+2^{27}q$ for all $q$, and one kernel evaluation of the checker over the list closes the chunk.
--
--   **Role.** Together with the other chunks and the refined residual `syracuse_descent_residual_twentyseven_mod32_mod2097152_after_step17_mod134217728` it reduces the open frontier leaf [`syracuse_descent_residual_twentyseven_mod32_mod2097152_after_step16_mod67108864`](https://prove2.me/theorems/be7d88ec-edf6-4cd4-aef7-5196be4d9650) by a case split on membership in the chunk lists; the chunks together remove $58040/369394\approx 15.7\%$ of the leaf's open classes modulo $2^{27}$ without bounding the starting value or the descent time.
--
--   **Formalization Note.** The map is the existing definition `syracuseStep`; the residue list is the published definition `syrStep17Chunk6`. The recursion-depth option only supports elaboration of the long literal. No monotonicity of the Syracuse map is asserted.
-- source:
--   Original computation of this contribution (explicit certified refinement of https://prove2.me/theorems/be7d88ec-edf6-4cd4-aef7-5196be4d9650 from modulus 2^26 to 2^27, split into 24 kernel-checked chunks; the residue table is computed, not quoted from the literature). Method: residue-class descent via the Proved theorem CollatzFrontier.syracuse_terminal_budget_of_descent, https://prove2.me/theorems/2513a4d3-77eb-4b93-9876-33755812122c; exact Syracuse definition https://prove2.me/theorems/2d5fcb43-85b2-4d75-beb8-3e236e66eac3.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Definitions.Def_syrStep17Chunk6

set_option maxRecDepth 16384

theorem syracuse_descent_twentyseven_mod32_mod2097152_step17_mod134217728_chunk6 (n : ℕ)
    (h : n % 134217728 ∈ syrStep17Chunk6) :
    syracuseStep^[17] n < n := by sorry
