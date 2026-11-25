-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_bfs_vertex_scan_counted
-- name    : WilliamsonShmoys.ram_bfs_vertex_scan_counted
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T02:23:08.337035+00:00
-- url     : https://prove2.me/theorems/127a3235-e147-4f28-ae27-1a5e0c61603b
-- title:
--   RAM vertex-scan loop of BFS with per-layer cost
-- statement:
--   This is the middle loop of the RAM breadth-first search used to compute Baker's levels: one BFS layer expansion over all vertices.
--
--   Let a program $p$ contain, at position $c$, the 27-instruction loop over vertices $u$ (cell 24, bound $n$ in cell 13). The edge table of the $n$-vertex graph is stored at odd-spaced addresses $E(v,j)=36+2vn+2j$, and the level labels $L(j)$ at $\mathrm{LVB}+2j$, where $\mathrm{LVB}\ge 36+2n^2$. A label $0$ means unvisited; otherwise it is the BFS distance plus one. For each $u$ whose label equals the current layer label $t\ge1$ (cell 15), the loop runs the row scan (`ram_bfs_row_scan`). That scan labels every unvisited neighbour $j$ of $u$ with $t+1$ (cell 14), where adjacency is the symmetrised relation "$E(u,j)\ge1$ or $E(j,u)\ge1$".
--
--   Started at the loop head with $u$ in cell 24, $r=n-u$ vertices remaining and the auxiliary pointer registers initialised, the program reaches $c+27$ within
--
--   $$9r+1+(14n+14)\cdot\#\{v: u\le v<n,\ L(v)=t\}$$
--
--   operations, so only vertices of the current layer pay for a row scan. For every $j<n$,
--
--   $$L'(j)=\begin{cases}t+1,&\text{if }L(j)=0\ \text{and}\ \exists v,\ u\le v<n,\ L(v)=t,\ \bigl(E(v,j)\ge1\vee E(j,v)\ge1\bigr),\\ L(j),&\text{otherwise.}\end{cases}$$
--
--   The flag cell 23 becomes $1$ exactly when some vertex was newly labelled, and is unchanged otherwise. All cells above 28 outside the label array, and all cells $\le15$, are unchanged, as are the constant registers 19, 20 and 28 and the real memory. Because the new label $t+1$ differs from $t$, vertices labelled during the pass are not expanded in the same pass, so the result is exactly one BFS layer step.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`. The if-conditions with existentials use classical decidability (`open Classical`).
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, p. 270 (BFS levels)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_bfs_vertex_scan_counted (p : List PlanarRAMInstruction) (c : ℕ)
    (hcode : CodeAt p c
    [natBranch 13 24 (c + 27) (c + 1),
      natLoad 22 27,
      natBranch 22 15 (c + 3) (c + 22),
      natBranch 15 22 (c + 4) (c + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (c + 8 + 14) (c + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (c + 8 + 5) (c + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (c + 8 + 5) (c + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (c + 8 + 7) (c + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (c + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump c])
    (n t LVB : ℕ) (ht : 1 ≤ t) (hLVB : 36 + 2 * n * n ≤ LVB) :
    ∀ (r u : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), u + r = n →
      M 13 = n → M 20 = 2 * n → M 24 = u → M 25 = 36 + 2 * u * n → M 26 = 36 + 2 * u →
      M 27 = LVB + 2 * u → M 28 = LVB → M 11 = 1 → M 12 = 0 → M 19 = 2 → M 15 = t → M 14 = t + 1 →
      ∃ τ, τ ≤ 9 * r + 1 + (14 * n + 14) *
          ∑ v ∈ Finset.range r, (if M (LVB + 2 * (u + v)) = t then 1 else 0) ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).pc = c + 27 ∧
        (∀ j, j < n → (planarRAMRun p ⟨c, M, R⟩ τ).natMem (LVB + 2 * j) =
          if M (LVB + 2 * j) = 0 ∧ ∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n)))
          then t + 1 else M (LVB + 2 * j)) ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 23 =
          (if ∃ v, u ≤ v ∧ v < n ∧ M (LVB + 2 * v) = t ∧ ∃ j, j < n ∧
              (1 ≤ M (36 + 2 * v * n + 2 * j) ∨ 1 ≤ M (36 + 2 * v + j * (2 * n))) ∧ M (LVB + 2 * j) = 0
            then 1 else M 23) ∧
        (∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨c, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≤ 15 → (planarRAMRun p ⟨c, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨c, M, R⟩ τ).natMem 20 = 2 * n ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).natMem 28 = LVB ∧
        (planarRAMRun p ⟨c, M, R⟩ τ).realMem = R := by sorry
