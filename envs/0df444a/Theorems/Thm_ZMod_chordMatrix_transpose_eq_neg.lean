-- Prove2me | Theorems.Thm_ZMod_chordMatrix_transpose_eq_neg
-- name    : ZMod.chordMatrix_transpose_eq_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c876661b-0d7b-5559-bfa5-a5132a40a7a7
-- title:
--   Antisymmetry of the chord-crossing matrix on ℤ/2m
-- statement:
--   Let $m$ be a nonzero natural number and let $a, b : \mathrm{Fin}\, m \to \mathbb{Z}/2m$ be two families of residues modulo $2m$, thought of as the two endpoints of $m$ chords of a $2m$-gon. The hypothesis `hdist` is that the map $\mathrm{Fin}\,m \times \mathrm{Bool} \to \mathbb{Z}/2m$ sending $(i,\mathrm{true})$ to $a\,i$ and $(i,\mathrm{false})$ to $b\,i$ is injective; equivalently, the $2m$ residues $a\,1,\dots,a\,m,b\,1,\dots,b\,m$ are pairwise distinct. Define the integer matrix $P \in \mathrm{Matrix}(\mathrm{Fin}\,m, \mathrm{Fin}\,m, \mathbb{Z})$ by
--   $$P_{ij} = [\,a\,j \neq a\,i \text{ and } (a\,j - a\,i).\mathrm{val} < (b\,i - a\,i).\mathrm{val}\,] - [\,b\,j \neq a\,i \text{ and } (b\,j - a\,i).\mathrm{val} < (b\,i - a\,i).\mathrm{val}\,],$$
--   where $[\;]$ denotes $1$ if the condition holds and $0$ otherwise and $(\cdot).\mathrm{val}$ is the representative in $\{0,\dots,2m-1\}$: thus $P_{ij}$ counts, with sign $+$ for the $a$-end and $-$ for the $b$-end, how many endpoints of the $j$-th chord lie strictly inside the arc running from $a\,i$ to $b\,i$ in the direction of increasing residue. The conclusion is that the transpose of $P$ equals $-P$, i.e. $P_{ji} = -P_{ij}$ for all $i,j$.
--
--   This is the combinatorial antisymmetry of the crossing (signed linking) matrix of a chord diagram with $2m$ distinct endpoints on a circle: two chords either nest, contributing $0$, or interlock, contributing $\pm 1$ with the sign reversed when the roles of the two chords are exchanged. It is used as the combinatorial input to [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw), where the chords are the identified sides of a polygon model and the arcs are the corresponding loops.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_chordMatrix_transpose_eq_neg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ZMod.chordMatrix_transpose_eq_neg {m : ℕ} [NeZero m]
    (a b : Fin m → ZMod (2 * m))
    (hdist : Function.Injective (fun p : Fin m × Bool => bif p.2 then a p.1 else b p.1)) :
    let P : Matrix (Fin m) (Fin m) ℤ := fun i j =>
      (if a j ≠ a i ∧ (a j - a i).val < (b i - a i).val then (1 : ℤ) else 0) -
      (if b j ≠ a i ∧ (b j - a i).val < (b i - a i).val then (1 : ℤ) else 0)
    P.transpose = -P := by sorry
