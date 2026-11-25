-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_baker_seg_levels
-- name    : WilliamsonShmoys.ram_baker_seg_levels
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T13:17:06.354965+00:00
-- url     : https://prove2.me/theorems/49565cea-d60b-5065-b4fe-ab8fb162a930
-- title:
--   BFS levels, residues and odd-cell clearing phase of the RAM Baker program
-- statement:
--   This phase computes the residues of Baker's levels modulo $k$ and clears the odd cells for the sandboxed solver. It runs from position $123$ to $207$ and consists of `ram_bfs_baker_levels`, `ram_level_mod_sweep`, `ram_zero_odd_cells` and three short glue blocks.
--
--   Assume the register layout produced by the previous phases: the off-diagonal edge bits at $36+2vn+2w$, a zero diagonal, $\mathrm{LVB}=16n^2+16n+48$, zero memory from $48+2n^2$ on, and zero odd real cells from $n$ on. Then within $40(n+1)^2+260$ operations the program reaches $207$ with
--
--   $$\mathrm{nat}(\mathrm{LVB}+2j)=\mathrm{bakerLevel}_G(j)\bmod k\qquad(G=\texttt{fromRel edge}).$$
--
--   On arrival every odd natural and real cell is $0$, while the edge table, cells $32,34,28$ ($n,k,\mathrm{LVB}$) and the even real cells other than $0$ are preserved.
--
--   **Formalization Note.** Code placement uses `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (Baker's PTAS for planar weighted independent set)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec
import Definitions.Def_WilliamsonShmoys_BakerLevel

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_baker_seg_levels (p : List PlanarRAMInstruction)
    (hc6 : CodeAt p 123 [natConst 29 0, natAdd 30 28 12, natBranch 13 29 (123 + 58) (123 + 3), natLoad 22 30, natBranch 22 12 (123 + 5) (123 + 55), natStore 30 11, natConst 15 1, natConst 14 2, natConst 23 0, natConst 24 0, natConst 25 36, natConst 26 36, natAdd 27 28 12, natBranch 13 24 (123 + 8 + 5 + 27) (123 + 8 + 5 + 1), natLoad 22 27, natBranch 22 15 (123 + 8 + 5 + 3) (123 + 8 + 5 + 22), natBranch 15 22 (123 + 8 + 5 + 4) (123 + 8 + 5 + 22), natConst 16 0, natAdd 17 25 12, natAdd 18 26 12, natAdd 21 28 12, natBranch 13 16 (123 + 8 + 5 + 8 + 14) (123 + 8 + 5 + 8 + 1), natLoad 22 17, natBranch 11 22 (123 + 8 + 5 + 8 + 5) (123 + 8 + 5 + 8 + 3), natLoad 22 18, natBranch 11 22 (123 + 8 + 5 + 8 + 5) (123 + 8 + 5 + 8 + 9), natLoad 22 21, natBranch 22 12 (123 + 8 + 5 + 8 + 7) (123 + 8 + 5 + 8 + 9), natStore 21 14, natAdd 23 11 12, natAdd 16 16 11, natAdd 17 17 19, natAdd 18 18 20, natAdd 21 21 19, jump (123 + 8 + 5 + 8), natAdd 24 24 11, natAdd 25 25 20, natAdd 26 26 19, natAdd 27 27 19, jump (123 + 8 + 5), natBranch 11 23 (123 + 8 + 33) (123 + 8 + 36), natAdd 15 15 11, natAdd 14 14 11, jump (123 + 8), natConst 24 0, natAdd 27 28 12, natBranch 13 24 (123 + 44 + 11) (123 + 44 + 3), natLoad 22 27, natBranch 22 12 (123 + 44 + 8) (123 + 44 + 5), natBranch 22 31 (123 + 44 + 6) (123 + 44 + 8), natAdd 22 22 31, natStore 27 22, natAdd 24 24 11, natAdd 27 27 19, jump (123 + 44 + 2), natAdd 29 29 11, natAdd 30 30 19, jump (123 + 2)])
    (hg1 : CodeAt p 181 [natAdd 16 34 12, natAdd 17 13 10])
    (hc7 : CodeAt p 183 [natConst 24 0, natAdd 27 28 12, natBranch 13 24 (183 + 12) (183 + 3), natLoad 22 27, natSub 22 22 17, natBranch 16 22 (183 + 6) (183 + 8), natSub 22 22 16, jump (183 + 5), natStore 27 22, natAdd 24 24 11, natAdd 27 27 19, jump (183 + 2)])
    (hg2 : CodeAt p 195 [natAdd 2 1 1, natConst 5 97, natAdd 2 2 5])
    (hc8 : CodeAt p 198 [natConst 0 1, natConst 4 2, natConst 6 0, realZero 0, natBranch 2 0 (198 + 9) (198 + 5), natStore 0 6, realStore 0 0, natAdd 0 0 4, jump (198 + 4)])
    (n k : ℕ) (hk : 0 < k) (edge : Fin n → Fin n → Bool) (M : ℕ → ℕ) (R : ℕ → ℝ)
    (h0 : M 0 = n) (h10 : M 10 = 2) (h11 : M 11 = 1) (h12 : M 12 = 0) (h13 : M 13 = n) (h19 : M 19 = 2)
    (h20 : M 20 = 2 * n) (h31 : M 31 = n + 1) (h28 : M 28 = (16 * (n * n) + 16 * n + 48)) (h1 : M 1 = n * n)
    (h32 : M 32 = n) (h34 : M 34 = k)
    (hE : ∀ v w : Fin n, v ≠ w → M (36 + 2 * v.val * n + 2 * w.val) = if edge v w then 1 else 0)
    (hD : ∀ v, v < n → M (36 + v * (2 * n + 2)) = 0)
    (hZ : ∀ a, 48 + 2 * (n * n) ≤ a → M a = 0)
    (hRo : ∀ a, a % 2 = 1 → n ≤ a → R a = 0) :
    ∃ τ, τ ≤ 40 * (n + 1) * (n + 1) + 260 ∧ (planarRAMRun p ⟨123, M, R⟩ τ).pc = 207 ∧
      (planarRAMRun p ⟨123, M, R⟩ τ).natMem 32 = n ∧ (planarRAMRun p ⟨123, M, R⟩ τ).natMem 34 = k ∧ (planarRAMRun p ⟨123, M, R⟩ τ).natMem 28 = (16 * (n * n) + 16 * n + 48) ∧
      (∀ j : Fin n, (planarRAMRun p ⟨123, M, R⟩ τ).natMem ((16 * (n * n) + 16 * n + 48) + 2 * j.val) =
        bakerLevel (SimpleGraph.fromRel (fun u v => edge u v = true)) j % k) ∧
      (∀ v w : Fin n, (planarRAMRun p ⟨123, M, R⟩ τ).natMem (36 + 2 * v.val * n + 2 * w.val) = M (36 + 2 * v.val * n + 2 * w.val)) ∧
      (∀ a, a % 2 = 1 → (planarRAMRun p ⟨123, M, R⟩ τ).natMem a = 0) ∧ (∀ a, a % 2 = 1 → (planarRAMRun p ⟨123, M, R⟩ τ).realMem a = 0) ∧
      (∀ a, a % 2 = 0 → a ≠ 0 → (planarRAMRun p ⟨123, M, R⟩ τ).realMem a = R a) := by sorry
