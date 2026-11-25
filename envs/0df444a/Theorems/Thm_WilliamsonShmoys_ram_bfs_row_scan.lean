-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_bfs_row_scan
-- name    : WilliamsonShmoys.ram_bfs_row_scan
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T00:24:12.431133+00:00
-- url     : https://prove2.me/theorems/fc13237b-8f15-4175-ab9a-6704743d61cc
-- title:
--   RAM row-scan loop of breadth-first search
-- statement:
--   This is the inner loop of the RAM breadth-first search for Baker's levels: one scan of an adjacency row.
--
--   Let a program $p$ contain, at position $b$, the 14-instruction loop over $w$ (cell 16, bound $n$ in cell 13). It reads the edge bits at addresses $\mathrm{pr}+2j$ (row $u$) and $\mathrm{pc}+jD$ (column $u$, with $D$ in cell 20) and the level label at $\mathrm{la}+2j$. When an edge bit is $\ge1$ and the label is $0$ (unvisited), it writes the new label held in cell 14 and sets the flag cell 23 to $1$.
--
--   Started at the loop head with $r=n-w$ iterations remaining, pointers $\mathrm{pr},\mathrm{pc},\mathrm{la}\ge32$, and the label region disjoint from the edge addresses, the loop reaches $b+14$ within $14r+1$ operations. For every $j<r$,
--
--   $$\mathrm{label}'(\mathrm{la}+2j)=\begin{cases}\text{cell }14,&\text{if }(E_{pr+2j}\ge1\ \vee\ E_{pc+jD}\ge1)\ \wedge\ \mathrm{label}(\mathrm{la}+2j)=0,\\ \mathrm{label}(\mathrm{la}+2j),&\text{otherwise.}\end{cases}$$
--
--   The flag becomes $1$ exactly when some label was written, and is unchanged otherwise. All other cells, except the loop registers and the scratch cell 22, are unchanged. Reading both row $u$ and column $u$ implements the symmetrised adjacency of `SimpleGraph.fromRel`.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, p. 270 (BFS levels)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction

theorem WilliamsonShmoys.ram_bfs_row_scan (p : List PlanarRAMInstruction) (b : ℕ)
    (hcode : CodeAt p b
      [natBranch 13 16 (b + 14) (b + 1), natLoad 22 17, natBranch 11 22 (b + 5) (b + 3), natLoad 22 18, natBranch 11 22 (b + 5) (b + 9), natLoad 22 21, natBranch 22 12 (b + 7) (b + 9), natStore 21 14, natAdd 23 11 12, natAdd 16 16 11, natAdd 17 17 19, natAdd 18 18 20, natAdd 21 21 19, jump b]) :
    ∀ (r w pr pc la : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), w + r = M 13 →
      M 16 = w → M 17 = pr → M 18 = pc → M 21 = la → M 11 = 1 → M 12 = 0 → M 19 = 2 →
      32 ≤ la → 32 ≤ pr → 32 ≤ pc →
      (∀ j j', j < r → j' < r → la + 2 * j ≠ pr + 2 * j' ∧ la + 2 * j ≠ pc + j' * M 20) →
      ∃ τ, τ ≤ 14 * r + 1 ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 14 ∧
        (∀ j, j < r → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (la + 2 * j) =
          if (1 ≤ M (pr + 2 * j) ∨ 1 ≤ M (pc + j * M 20)) ∧ M (la + 2 * j) = 0 then M 14
          else M (la + 2 * j)) ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).natMem 23 =
          (if ∃ j, j < r ∧ (1 ≤ M (pr + 2 * j) ∨ 1 ≤ M (pc + j * M 20)) ∧ M (la + 2 * j) = 0 then 1
            else M 23) ∧
        (∀ a, a ≠ 16 → a ≠ 17 → a ≠ 18 → a ≠ 21 → a ≠ 22 → a ≠ 23 → (∀ j, j < r → a ≠ la + 2 * j) →
          (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨b, M, R⟩ τ).realMem = R := by sorry
