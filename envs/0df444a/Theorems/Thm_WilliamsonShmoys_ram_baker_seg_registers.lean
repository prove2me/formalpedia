-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_baker_seg_registers
-- name    : WilliamsonShmoys.ram_baker_seg_registers
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T13:17:20.575662+00:00
-- url     : https://prove2.me/theorems/eaf82690-65b1-4fa5-ad9b-945b6704a3f2
-- title:
--   Register set-up and diagonal clearing before the RAM BFS
-- statement:
--   This 28-instruction block prepares the registers for the RAM breadth-first search and clears the diagonal of the edge table, so that the table encodes the loop-free graph $G$.
--
--   Started at its first position $b$ with $n$ in cell $0$ and $2,1,0$ in cells $10,11,12$, it reaches $b+28$ within $9n+24$ operations. It sets cells $13,20,19,31$ to $n,2n,2,n+1$, cell $1$ to $n^2$, and cell $28$ to
--
--   $$\mathrm{LVB}=16n^2+16n+48 .$$
--
--   It also sets $\mathrm{nat}(36+v(2n+2))=0$ for all $v<n$, which is the diagonal entry $(v,v)$ of the relocated edge table. All other cells, and the real memory, are unchanged.
--
--   **Formalization Note.** Code placement uses `CodeAt` from `Def_WilliamsonShmoys_RAMExec`.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (Baker's PTAS for planar weighted independent set)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_baker_seg_registers (p : List PlanarRAMInstruction) (b : ℕ)
    (hcode : CodeAt p b
    [natAdd 13 0 12,
      natAdd 20 0 0,
      natConst 19 2,
      natAdd 31 0 11,
      natConst 1 0,
      natConst 3 0,
      natBranch 0 3 (b + 10) (b + 7),
      natAdd 1 1 0,
      natAdd 3 3 11,
      jump (b + 6),
      natAdd 28 1 1,
      natAdd 28 28 28,
      natAdd 28 28 28,
      natAdd 28 28 28,
      natAdd 5 20 20,
      natAdd 5 5 5,
      natAdd 5 5 5,
      natAdd 28 28 5,
      natConst 5 48,
      natAdd 28 28 5,
      natConst 2 36,
      natAdd 3 20 10,
      natConst 4 0,
      natBranch 0 4 (b + 28) (b + 24),
      natStore 2 12,
      natAdd 2 2 3,
      natAdd 4 4 11,
      jump (b + 23)])
    (n : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ) (h0 : M 0 = n) (h10 : M 10 = 2) (h11 : M 11 = 1) (h12 : M 12 = 0) :
    ∃ τ, τ ≤ 9 * n + 24 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).pc = b + 28 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 13 = n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 20 = 2 * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 19 = 2 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 31 = n + 1 ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 11 = 1 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 12 = 0 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 10 = 2 ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 0 = n ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).natMem 1 = n * n ∧ (planarRAMRun p ⟨b, M, R⟩ τ).natMem 28 = 16 * (n * n) + 16 * n + 48 ∧
      (∀ v, v < n → (planarRAMRun p ⟨b, M, R⟩ τ).natMem (36 + v * (2 * n + 2)) = 0) ∧
      (∀ a, a ≠ 13 → a ≠ 20 → a ≠ 19 → a ≠ 31 → a ≠ 1 → a ≠ 3 → a ≠ 28 → a ≠ 5 → a ≠ 2 → a ≠ 4 →
        (∀ v, v < n → a ≠ 36 + v * (2 * n + 2)) → (planarRAMRun p ⟨b, M, R⟩ τ).natMem a = M a) ∧
      (planarRAMRun p ⟨b, M, R⟩ τ).realMem = R := by sorry
