-- Prove2me | Theorems.Thm_huangMatrix_entry_abs
-- name    : huangMatrix_entry_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-04-23T04:02:36.612641+00:00
-- url     : https://prove2.me/theorems/2ecf55f3-d656-4497-ba60-19fb4d58483f
-- statement:
--   Entries of Huang's matrix are +-1 on hypercube edges and 0 elsewhere: |huangMatrix n u v| = 1 if Hypercube.Adj n u v else 0. Bridges the algebraic matrix with the combinatorial graph structure.
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the sensitivity conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Definitions.Def_Hypercube
import Definitions.Def_huangMatrix

/-!
# huangMatrix entry absolute value

The entries of `huangMatrix n` are ±1 on edges of the hypercube and 0 elsewhere.
Equivalently: `|A_n[u,v]| = 1 if u ~ v in Q_n, else 0`. Ties the algebraic matrix
to the combinatorial graph structure — needed whenever we bridge `huangMatrix`
with `Hypercube.Adj` (e.g. when applying the generic spectral-graph bound
`max_degree_ge_lambda_max` to a principal submatrix of `huangMatrix`).
-/

/-- `|A_n[u,v]| = 1` if `u` and `v` are adjacent in `Q_n`, else `0`. -/

theorem huangMatrix_entry_abs :
    ∀ (n : ℕ) (u v : Fin n → Bool),
      |huangMatrix n u v| = if Hypercube.Adj n u v then 1 else 0 := by sorry
