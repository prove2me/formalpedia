-- Prove2me | Theorems.Thm_WilliamsonShmoys_ram_best_copy_select
-- name    : WilliamsonShmoys.ram_best_copy_select
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T08:22:53.773845+00:00
-- url     : https://prove2.me/theorems/a82d06f6-b45c-5660-84b4-f02d8b257961
-- title:
--   RAM selection of the best copy after the disjoint-union solver call
-- statement:
--   After the single solver call on the disjoint union of the $k$ masked graphs, this RAM program picks the copy of largest weight. That copy is the best shift class of Baker's technique.
--
--   Let a program $p$ contain, at position $q$, the 50-instruction program. On entry cells 32, 34, 28 hold $n$, $k\ge1$ and an even $\mathrm{LVB}\ge40$. Put $N=kn$ and $B_c=5+2N^2+2cn$. The solver's output bit of union vertex $cn+v$ sits in the odd host cell $B_c+2v$ (the odd-cell image of solver cell $2+N^2+cn+v$). The residue $m(v)$ sits at $\mathrm{LVB}+2v$ and the weight $w(v)$ in the real cell $32+2v$. Define
--
--   $$W_c=\sum_{v<n}\bigl[\,\mathrm{bit}(B_c+2v)\ge1\ \wedge\ m(v)\ne c\,\bigr]\,w(v).$$
--
--   The program reaches $q+50$ within $(16n+24)k+20$ operations. On exit cell 20 holds some $c^\*<k$ with
--
--   $$W_c\le W_{c^\*}\qquad\text{for all } c<k,$$
--
--   and cell 22 holds $B_{c^\*}$. All odd cells and all even cells $\ge40$ are unchanged, and so are all real cells $\ge6$. It computes $N$ and $N^2$ by repeated addition, sums $W_c$ for each copy with real additions, and keeps the first maximum using `realBranch`.
--
--   **Formalization Note.** Code placement is `CodeAt` from `Def_WilliamsonShmoys_RAMExec`. The predicate uses $\ge1$ for the bit; for solver outputs bounded by $1$ this is the same as bit $=1$.
-- source:
--   RAM implementation of Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2 (choose the best of the k shifted solutions)

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false
open WilliamsonShmoys PlanarRAMInstruction
open Classical

theorem WilliamsonShmoys.ram_best_copy_select (p : List PlanarRAMInstruction) (q : ℕ)
    (hcode : CodeAt p q
    [natConst 0 0,
      natConst 2 1,
      natConst 4 2,
      natAdd 24 32 32,
      natAdd 18 28 24,
      natConst 26 0,
      natConst 6 0,
      natBranch 34 6 (q + 11) (q + 8),
      natAdd 26 26 32,
      natAdd 6 6 2,
      jump (q + 7),
      natConst 30 0,
      natConst 6 0,
      natBranch 26 6 (q + 17) (q + 14),
      natAdd 30 30 26,
      natAdd 6 6 2,
      jump (q + 13),
      natAdd 30 30 30,
      natConst 8 5,
      natAdd 14 30 8,
      natConst 6 0,
      natConst 20 0,
      natAdd 22 14 0,
      realZero 4,
      natBranch 34 6 (q + 50) (q + 25),
      realZero 2,
      natAdd 10 28 0,
      natConst 16 32,
      natAdd 12 14 0,
      natBranch 18 10 (q + 41) (q + 30),
      natLoad 8 12,
      natBranch 2 8 (q + 32) (q + 37),
      natLoad 8 10,
      natBranch 8 6 (q + 34) (q + 35),
      natBranch 6 8 (q + 37) (q + 35),
      realLoad 0 16,
      realAdd 2 2 0,
      natAdd 10 10 4,
      natAdd 12 12 4,
      natAdd 16 16 4,
      jump (q + 29),
      natBranch 6 0 (q + 43) (q + 42),
      realBranch 2 4 (q + 47) (q + 43),
      realZero 4,
      realAdd 4 4 2,
      natAdd 20 6 0,
      natAdd 22 14 0,
      natAdd 14 14 24,
      natAdd 6 6 2,
      jump (q + 24)])
    (n k LVB : ℕ) (hk : 0 < k) (hLe : LVB % 2 = 0) (hL : 40 ≤ LVB)
    (M : ℕ → ℕ) (R : ℕ → ℝ) (h32 : M 32 = n) (h34 : M 34 = k) (h28 : M 28 = LVB) :
    ∃ τ, τ ≤ (16 * n + 24) * k + 20 ∧ (planarRAMRun p ⟨q, M, R⟩ τ).pc = q + 50 ∧ (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 < k ∧
      (planarRAMRun p ⟨q, M, R⟩ τ).natMem 22 = 5 + 2 * (k * n) * (k * n) + 2 * (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 * n ∧
      (∀ c', c' < k → (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * c' * n + 2 * j) ∧ M (LVB + 2 * j) ≠ c' then R (32 + 2 * j) else 0) ≤ (∑ j ∈ Finset.range n, if 1 ≤ M (5 + 2 * (k * n) * (k * n) + 2 * (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 * n + 2 * j) ∧ M (LVB + 2 * j) ≠ (planarRAMRun p ⟨q, M, R⟩ τ).natMem 20 then R (32 + 2 * j) else 0)) ∧
      (∀ a, (a % 2 = 1 ∨ 40 ≤ a) → (planarRAMRun p ⟨q, M, R⟩ τ).natMem a = M a) ∧
      (∀ a, 6 ≤ a → (planarRAMRun p ⟨q, M, R⟩ τ).realMem a = R a) := by sorry
