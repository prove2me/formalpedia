-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_bfs_finalize_sweep
-- name    : WilliamsonShmoys.ram_bfs_finalize_sweep
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T02:41:17.403388+00:00
-- url     : https://prove2.me/theorems/40b5dc89-9c86-5606-b0bc-1858faceb5e8
-- title:
--   RAM label finalisation sweep after a BFS tree
-- statement:
--   This is the finalisation sweep of the RAM breadth-first search for Baker's levels. It runs after each BFS tree is complete and shifts the labels of the finished component out of the range used by later layer labels.
--
--   Let a program $p$ contain, at position $g$, the 11-instruction loop over $w=0,\dots,n-1$ (cells 24 and 27). The labels sit at $L(j)=\mathrm{LVB}+2j$, and cell 31 holds $n+1$. Started at $g$ with $n$ in cell 13, $\mathrm{LVB}\ge36$ in cell 28, and the constants $1,0,2$ in cells 11, 12, 19, the program reaches $g+11$ within $9n+3$ operations, and for every $j<n$
--
--   $$L'(j)=\begin{cases}L(j)+n+1,&1\le L(j)\le n+1,\\ L(j),&\text{otherwise.}\end{cases}$$
--
--   All cells other than 22, 24, 27 and the label array are unchanged, as is the real memory. After the sweep, every finished vertex has label $n+2+\mathrm{dist}\ge n+2$. Such a label is never equal to a layer label $t\le n$ of a later search, so finished vertices are never rescanned.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, p. 270 (BFS levels)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_bfs_finalize_sweep (p : List PlanarRAMInstruction) (g : ℕ)
    (hcode : CodeAt p g
    [natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (g + 11) (g + 3),
      natLoad 22 27,
      natBranch 22 12 (g + 8) (g + 5),
      natBranch 22 31 (g + 6) (g + 8),
      natAdd 22 22 31,
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (g + 2)])
    (n LVB : ℕ) (hLVB : 36 ≤ LVB) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h28 : M 28 = LVB) (h11 : M 11 = 1) (h12 : M 12 = 0) (h19 : M 19 = 2)
    (h31 : M 31 = n + 1) :
    ∃ τ, τ ≤ 9 * n + 3 ∧
      (planarRAMRun p ⟨g, M, R⟩ τ).pc = g + 11 ∧
      (∀ j, j < n → (planarRAMRun p ⟨g, M, R⟩ τ).natMem (LVB + 2 * j) =
        if 1 ≤ M (LVB + 2 * j) ∧ M (LVB + 2 * j) ≤ n + 1 then M (LVB + 2 * j) + (n + 1)
        else M (LVB + 2 * j)) ∧
      (∀ a, a ≠ 22 → a ≠ 24 → a ≠ 27 → (∀ j, j < n → a ≠ LVB + 2 * j) →
        (planarRAMRun p ⟨g, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨g, M, R⟩ τ).realMem = R := by sorry
