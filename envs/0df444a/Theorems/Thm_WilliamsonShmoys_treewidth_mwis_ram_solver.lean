-- Prove2me | Theorems.Thm_WilliamsonShmoys_treewidth_mwis_ram_solver
-- name    : WilliamsonShmoys.treewidth_mwis_ram_solver
-- status  : Open
-- author  : @amirh
-- created : 2026-10-30T23:33:31.863667+00:00
-- url     : https://prove2.me/theorems/b9d0cd0e-433c-4894-b390-137f5f5ac8cd
-- title:
--   RAM program: exact maximum-weight independent set for tree-width $\le w$ in $C\,2^{dw}(n+1)^2$ operations
-- statement:
--   Exact maximum-weight independent set on graphs of bounded tree-width, computed by one fixed program for the unit-cost real RAM of `WilliamsonShmoys_PlanarIndependentSetRAM`.
--
--   There are a finite program $P$ and constants $C,d>0$ with the following property. Let $w\ge 0$ and $n\ge 0$ be integers, let $E:\{0,\dots,n-1\}^2\to\{0,1\}$ be an adjacency table, and let $\omega:\{0,\dots,n-1\}\to\mathbb R$ be an arbitrary real weight vector. Let $G$ be the simple graph on $\{0,\dots,n-1\}$ in which distinct vertices $u,v$ are adjacent if and only if $E(u,v)=1$ or $E(v,u)=1$, and write $\omega(X)=\sum_{v\in X}\omega(v)$. Start $P$ on the standard input layout: natural cells $0$ and $1$ hold $n$ and $w$, the next $n^2$ natural cells hold $E$ row by row, real cells $0,\dots,n-1$ hold $\omega$, and every other cell holds $0$. If $G$ has tree-width at most $w$, then after some number $t$ of operations with
--
--   $$t+1\le C\,2^{dw}\,(n+1)^2$$
--
--   the program counter of $P$ points at a `halt` instruction, and at that moment:
--
--   1. each of the $n$ output cells (natural cells $2+n^2,\dots,1+n^2+n$) contains $0$ or $1$;
--   2. the set $A$ of vertices whose output cell contains $1$ is an independent set of $G$;
--   3. $A$ has maximum weight among all independent sets of $G$:
--
--   $$\omega(S)\le\omega(A)\qquad\text{for every independent set } S \text{ of } G.$$
--
--   This is the exact subproblem that the algorithmic half of Baker's PTAS solves once per shift (Williamson–Shmoys, Section 10.2, proof of Theorem 10.11): maximum-weight independent set on a graph of tree-width $O(k)$, with running time $2^{O(k)}n^2$. The program is given the width bound $w$ (in the cell that holds the accuracy parameter $k$ in the band problem) but no tree decomposition. With $w=3k$ it supplies the per-shift solver for `WilliamsonShmoys.band_treewidth_ram_solver`, and it is a reusable statement of the classical fact that weighted independent set is solvable in time single-exponential in the tree-width.
--
--   **Formalization Note** Tree-width at most $w$ is `RobertsonSeymour1986.GM5.TreewidthLE`. The graph is `SimpleGraph.fromRel` of the table, so the table need not be symmetric and its diagonal is ignored. Weights may be negative, in which case the empty set can be optimal. The input layout, the output bitmap, the step function and the halting convention are exactly those of `WilliamsonShmoys.band_treewidth_ram_solver`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272, https://doi.org/10.1017/CBO9780511921735: for each shift the algorithm solves maximum-weight independent set exactly on a graph of tree-width O(k) by finding a tree decomposition and running dynamic programming, O(2^{O(k)} n^2) time. Standard algorithms for the two steps: a tree decomposition of width at most 4w+4 in time 2^{O(w)} n^2 (N. Robertson and P. D. Seymour, Graph Minors XIII. The disjoint paths problem, J. Combin. Theory Ser. B 63 (1995) 65-110, https://doi.org/10.1006/jctb.1995.1006; textbook presentation in M. Cygan et al., Parameterized Algorithms, Springer 2015, Section 7.6), and the weighted independent set dynamic program over a tree decomposition in time 2^{O(w)} n (Cygan et al., Section 7.3.1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false
open scoped BigOperators

namespace WilliamsonShmoys
theorem treewidth_mwis_ram_solver :
    ∃ (program : List PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (w n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        RobertsonSeymour1986.GM5.TreewidthLE G w →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * w) * (n + 1) ^ 2 ∧
          let result := planarRAMRun program (planarRAMInput n w edge weight) t
          program[result.pc]? = some PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          G.IsIndepSet (planarRAMOutput n result : Set (Fin n)) ∧
          ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
            ∑ i ∈ S, weight i ≤ ∑ i ∈ planarRAMOutput n result, weight i := by sorry
end WilliamsonShmoys
