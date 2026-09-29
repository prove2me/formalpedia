-- Prove2me | Theorems.Thm_Erdos180_subdivisionPoint_pair_incidence
-- name    : Erdos180.subdivisionPoint_pair_incidence
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:06:18.213303+00:00
-- url     : https://prove2.me/theorems/d434dc8e-120b-41da-9978-13b140e5a8c3
-- title:
--   A copy of $S_k$ based at points: the joining line
-- statement:
--   Let $S_k$ embed into the incidence graph $I_q$ so that a base lands on the point $p$ and a
--   centre on the point $c$. Then the subdivision vertex between them lands on a line $L$ incident
--   to both $p$ and $c$.
--
--   Since $I_q$ is bipartite with sides $\mathcal{P}$ and $\mathcal{M}$, a copy of $S_k$ whose bases
--   and centres are points must send the subdivision vertices to lines. This is the concrete form
--   of Lemma 3.1(2): the $k$ centres of a copy of $S_k$ with base set $T$ are exactly common
--   centres of $T$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1869-L1895

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionPoint_pair_incidence
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    ∃ L : SymplecticLine K,
      copy (.inr (base, center)) = .inr L ∧
        p.1 ≤ L.1 ∧ c.1 ≤ L.1 := by sorry
