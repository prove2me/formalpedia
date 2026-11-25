-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_bfs_layer_loop
-- name    : WilliamsonShmoys.ram_bfs_layer_loop
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T02:41:21.421231+00:00
-- url     : https://prove2.me/theorems/6afbc30d-13d4-41f1-a3e6-404a1539ec51
-- title:
--   RAM layer loop of breadth-first search
-- statement:
--   This is the layer loop of the RAM breadth-first search for Baker's levels: it grows one BFS tree from a root $r$, one distance layer per pass.
--
--   Let a program $p$ contain, at position $d$, the 36-instruction loop. Each pass resets the flag cell 23 and the vertex-scan registers, runs the vertex scan (`ram_bfs_vertex_scan_counted`) for the current layer label $t$ (cell 15, with $t+1$ in cell 14), and then either increments $t$ and repeats (if the flag is set) or exits at $d+36$. The graph $G$ on $\{0,\dots,n-1\}$ is encoded by edge cells: $E(v,j)\ge1$ or $E(j,v)\ge1$ exactly when $G.\mathrm{Adj}\,v\,j$. Level labels $L(j)$ sit at $\mathrm{LVB}+2j$ with $\mathrm{LVB}\ge36+2n^2$.
--
--   Assume $1\le t\le n$ and that some vertex has $\mathrm{dist}(r,\cdot)+1=t$. Assume the labels satisfy the BFS invariant: a vertex $j$ reachable from $r$ has $L(j)=\mathrm{dist}(r,j)+1$ if $\mathrm{dist}(r,j)+1\le t$ and $L(j)=0$ otherwise, and an unreachable vertex has $L(j)=0$ or $L(j)\ge n+2$. Then the program reaches $d+36$ within
--
--   $$(23n+24)\cdot\#\{j:\ j \text{ reachable from } r,\ t\le \mathrm{dist}(r,j)+1\}$$
--
--   operations. Afterwards
--
--   $$L'(j)=\begin{cases}\mathrm{dist}(r,j)+1,& j\text{ reachable from }r,\\ L(j),&\text{otherwise,}\end{cases}$$
--
--   and all cells above 28 outside the label array, all cells $\le13$, the registers 19, 20, 28 and the real memory are unchanged. The cost is linear in $n$ per vertex of the component, which is what keeps Baker's level computation within $O(n^2)$ overall.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`. `G.dist` is Mathlib's `SimpleGraph.dist`. The termination fuel $f$ only needs $n+1\le t+f$.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, p. 270 (BFS levels)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_bfs_layer_loop (p : List PlanarRAMInstruction) (d : ℕ)
    (hcode : CodeAt p d
    [natConst 23 0,
      natConst 24 0,
      natConst 25 36,
      natConst 26 36,
      natAdd 27 28 12,
      natBranch 13 24 (d + 5 + 27) (d + 5 + 1),
      natLoad 22 27,
      natBranch 22 15 (d + 5 + 3) (d + 5 + 22),
      natBranch 15 22 (d + 5 + 4) (d + 5 + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (d + 5 + 8 + 14) (d + 5 + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (d + 5 + 8 + 5) (d + 5 + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (d + 5 + 8 + 5) (d + 5 + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (d + 5 + 8 + 7) (d + 5 + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (d + 5 + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump (d + 5),
      natBranch 11 23 (d + 33) (d + 36),
      natAdd 15 15 11,
      natAdd 14 14 11,
      jump d])
    (n LVB : ℕ) (hLVB : 36 + 2 * n * n ≤ LVB) (G : SimpleGraph (Fin n)) (r : Fin n) :
    ∀ (f t : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), n + 1 ≤ t + f → 1 ≤ t → t ≤ n →
      M 13 = n → M 20 = 2 * n → M 28 = LVB → M 11 = 1 → M 12 = 0 → M 19 = 2 → M 15 = t → M 14 = t + 1 →
      (∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j) →
      (∃ w, G.Reachable r w ∧ G.dist r w + 1 = t) →
      (∀ j : Fin n, if G.Reachable r j then
          M (LVB + 2 * (j : ℕ)) = (if G.dist r j + 1 ≤ t then G.dist r j + 1 else 0)
        else (M (LVB + 2 * (j : ℕ)) = 0 ∨ n + 2 ≤ M (LVB + 2 * (j : ℕ)))) →
      ∃ τ, τ ≤ (23 * n + 24) * (Finset.univ.filter (fun j : Fin n => G.Reachable r j ∧ t ≤ G.dist r j + 1)).card ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).pc = d + 36 ∧
        (∀ j : Fin n, (planarRAMRun p ⟨d, M, R⟩ τ).natMem (LVB + 2 * (j : ℕ)) =
          if G.Reachable r j then G.dist r j + 1 else M (LVB + 2 * (j : ℕ))) ∧
        (∀ a, 28 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨d, M, R⟩ τ).natMem a = M a) ∧
        (∀ a, a ≤ 13 → (planarRAMRun p ⟨d, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨d, M, R⟩ τ).natMem 20 = 2 * n ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).natMem 28 = LVB ∧
        (planarRAMRun p ⟨d, M, R⟩ τ).realMem = R := by sorry
