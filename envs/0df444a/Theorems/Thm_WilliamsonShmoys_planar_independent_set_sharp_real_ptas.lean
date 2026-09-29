-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_independent_set_sharp_real_ptas
-- name    : WilliamsonShmoys.planar_independent_set_sharp_real_ptas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:18:01.410618+00:00
-- url     : https://prove2.me/theorems/5f2b7b7f-6608-4d97-818b-e39162ac138b
-- title:
--   Theorem 10.11: planar weighted independent-set PTAS
-- statement:
--   One finite RAM program and absolute positive constants give, for every positive real accuracy, planar graph size, adjacency table, and nonnegative real weight vector, a halting independent-set output of weight at least (1−ε) times every independent set, within C·2^(d·max(1,⌈1/ε⌉))·(n+1)² unit-cost operations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Theorem 10.11, PDF/manuscript p. 271; weighted problem p. 269 and proof context pp. 270–272. https://doi.org/10.1017/CBO9780511921735.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM

set_option autoImplicit false
open scoped BigOperators

namespace WilliamsonShmoys
theorem planar_independent_set_sharp_real_ptas :
    ∃ (program : List PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (ε : ℝ), 0 < ε →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        let k := max 1 ⌈ε⁻¹⌉₊
        HasPlanarDrawing G → (∀ i, 0 ≤ weight i) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := planarRAMRun program (planarRAMInput n k edge weight) t
          program[result.pc]? = some PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          G.IsIndepSet (planarRAMOutput n result : Set (Fin n)) ∧
          ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
            (1 - ε) * (∑ i ∈ S, weight i) ≤
              ∑ i ∈ planarRAMOutput n result, weight i := by sorry
end WilliamsonShmoys
