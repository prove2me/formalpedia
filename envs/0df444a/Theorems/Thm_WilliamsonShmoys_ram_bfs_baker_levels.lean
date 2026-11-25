-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_bfs_baker_levels
-- name    : WilliamsonShmoys.ram_bfs_baker_levels
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T02:51:29.60647+00:00
-- url     : https://prove2.me/theorems/6d41fdd4-bff4-4f9e-8034-a1bb2e74bc03
-- title:
--   RAM computation of Baker's BFS levels in quadratic time
-- statement:
--   This is the complete RAM computation of Baker's breadth-first-search levels used in the planar PTAS of Williamson–Shmoys, Section 10.2: every vertex gets its distance from the root of its connected component in $O(n^2)$ operations.
--
--   Let a program $p$ contain, at position $e$, the 58-instruction root loop. It scans $u=0,\dots,n-1$ (cells 29, 30). Whenever the label of $u$ is still $0$, it sets that label to $1$ and grows a BFS tree from $u$ with the layer loop (`ram_bfs_layer_loop`) at $e+8$. It then runs the finalisation sweep (`ram_bfs_finalize_sweep`) at $e+44$. The graph $G$ on $\{0,\dots,n-1\}$ is encoded by edge cells: $E(v,j)=36+2vn+2j$, and $E(v,j)\ge1$ or $E(j,v)\ge1$ exactly when $G.\mathrm{Adj}\,v\,j$. Labels sit at $L(j)=\mathrm{LVB}+2j$ with $\mathrm{LVB}\ge36+2n^2$.
--
--   Started at $e$ with all labels $0$, with $n$, $2n$, $\mathrm{LVB}$, $1$, $0$, $2$, $n+1$ in cells 13, 20, 28, 11, 12, 19, 31, the program reaches $e+58$ within $32n^2+36n+3$ operations. Afterwards, for every vertex $j$,
--
--   $$L'(j)=n+2+\mathrm{bakerLevel}_G(j),\qquad \mathrm{bakerLevel}_G(j)=\mathrm{dist}_G(\mathrm{bakerRoot}_G(j),\,j),$$
--
--   where $\mathrm{bakerRoot}_G(j)$ is the least vertex of the component of $j$. All cells above 30 outside the label array, all cells $\le13$, the registers 19, 20, 28 and the real memory are unchanged. This provides, within the quadratic time budget, the level partition $L_0,L_1,\dots$ on which Baker's shifting technique is built.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`. `bakerRoot` and `bakerLevel` are from `Def_WilliamsonShmoys_BakerLevel`. The offset $n+2$ keeps finished labels disjoint from the layer labels $t\le n$ of later searches.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, p. 270 (BFS levels)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Definitions.Def_WilliamsonShmoys_BakerLevel

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_bfs_baker_levels (p : List PlanarRAMInstruction) (e : ℕ)
    (hcode : CodeAt p e
    [natConst 29 0,
      natAdd 30 28 12,
      natBranch 13 29 (e + 58) (e + 3),
      natLoad 22 30,
      natBranch 22 12 (e + 5) (e + 55),
      natStore 30 11,
      natConst 15 1,
      natConst 14 2,
      natConst 23 0,
      natConst 24 0,
      natConst 25 36,
      natConst 26 36,
      natAdd 27 28 12,
      natBranch 13 24 (e + 8 + 5 + 27) (e + 8 + 5 + 1),
      natLoad 22 27,
      natBranch 22 15 (e + 8 + 5 + 3) (e + 8 + 5 + 22),
      natBranch 15 22 (e + 8 + 5 + 4) (e + 8 + 5 + 22),
      natConst 16 0,
      natAdd 17 25 12,
      natAdd 18 26 12,
      natAdd 21 28 12,
      natBranch 13 16 (e + 8 + 5 + 8 + 14) (e + 8 + 5 + 8 + 1),
      natLoad 22 17,
      natBranch 11 22 (e + 8 + 5 + 8 + 5) (e + 8 + 5 + 8 + 3),
      natLoad 22 18,
      natBranch 11 22 (e + 8 + 5 + 8 + 5) (e + 8 + 5 + 8 + 9),
      natLoad 22 21,
      natBranch 22 12 (e + 8 + 5 + 8 + 7) (e + 8 + 5 + 8 + 9),
      natStore 21 14,
      natAdd 23 11 12,
      natAdd 16 16 11,
      natAdd 17 17 19,
      natAdd 18 18 20,
      natAdd 21 21 19,
      jump (e + 8 + 5 + 8),
      natAdd 24 24 11,
      natAdd 25 25 20,
      natAdd 26 26 19,
      natAdd 27 27 19,
      jump (e + 8 + 5),
      natBranch 11 23 (e + 8 + 33) (e + 8 + 36),
      natAdd 15 15 11,
      natAdd 14 14 11,
      jump (e + 8),
      natConst 24 0,
      natAdd 27 28 12,
      natBranch 13 24 (e + 44 + 11) (e + 44 + 3),
      natLoad 22 27,
      natBranch 22 12 (e + 44 + 8) (e + 44 + 5),
      natBranch 22 31 (e + 44 + 6) (e + 44 + 8),
      natAdd 22 22 31,
      natStore 27 22,
      natAdd 24 24 11,
      natAdd 27 27 19,
      jump (e + 44 + 2),
      natAdd 29 29 11,
      natAdd 30 30 19,
      jump (e + 2)])
    (n LVB : ℕ) (hLVB : 36 + 2 * n * n ≤ LVB) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h13 : M 13 = n) (h20 : M 20 = 2 * n) (h28 : M 28 = LVB) (h11 : M 11 = 1) (h12 : M 12 = 0)
    (h19 : M 19 = 2) (h31 : M 31 = n + 1)
    (hadj : ∀ v j : Fin n, (1 ≤ M (36 + 2 * (v : ℕ) * n + 2 * (j : ℕ)) ∨ 1 ≤ M (36 + 2 * (v : ℕ) + (j : ℕ) * (2 * n))) ↔ G.Adj v j)
    (hzero : ∀ j, j < n → M (LVB + 2 * j) = 0) :
    ∃ τ, τ ≤ 32 * n * n + 36 * n + 3 ∧
      (planarRAMRun p ⟨e, M, R⟩ τ).pc = e + 58 ∧
      (∀ j : Fin n, (planarRAMRun p ⟨e, M, R⟩ τ).natMem (LVB + 2 * (j : ℕ)) = n + 2 + bakerLevel G j) ∧
      (∀ a, 30 < a → (∀ j, j < n → a ≠ LVB + 2 * j) → (planarRAMRun p ⟨e, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, a ≤ 13 → (planarRAMRun p ⟨e, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨e, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨e, M, R⟩ τ).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨e, M, R⟩ τ).natMem 28 = LVB ∧ (planarRAMRun p ⟨e, M, R⟩ τ).realMem = R := by sorry
