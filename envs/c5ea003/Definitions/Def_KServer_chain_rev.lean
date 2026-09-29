-- Prove2me | Definitions.Def_KServer_chain_rev
-- name    : KServer_chain_rev
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T13:24:39.937322+00:00
-- url     : https://prove2.me/theorems/3e8ca77f-cb25-4cc3-acf8-f881d6e71418
-- title:
--   Reversal isometry of the three-copy chain
-- statement:
--   Let $X$ be a metric space with marked points $s \neq t$, and let $C_3(X;s,t)$ denote the three-copy chain: three copies of $X$ glued in a row (copy $0$'s $t$ to copy $1$'s $s$, copy $1$'s $t$ to copy $2$'s $s$), with start point copy $0$'s $s$ and stop point copy $2$'s $t$. The chain traversed backwards is the chain with the marks swapped: there is a bijection $$\mathrm{rev} : C_3(X;s,t) \to C_3(X;t,s)$$ sending copy $i$ to copy $2-i$ (each copy mapped identically, junction representatives to junction representatives) which preserves distances and exchanges the endpoints: $\mathrm{rev}(\mathrm{start}) = \mathrm{stop}$ and $\mathrm{rev}(\mathrm{stop}) = \mathrm{start}$, and $\mathrm{rev} \circ \mathrm{rev} = \mathrm{id}$. This is the distance-preserving bijection used to transport a chunk system of the reversed orientation onto backwards-traversed copies inside the BCR level step. We also record definitional unfoldings of the two- and three-copy chain distances to iterated glue distances.
-- source:
--   BCR randomized k-server lower bound, theta-space geometry layer

import Mathlib
import Definitions.Def_KServer_glue2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

/-! ### Reversal of the three-copy path

The `(s,t)`-chain traversed backwards is the `(t,s)`-chain: copy `i` maps
to copy `2-i`, each copy mapped identically, junction representatives to
junction representatives, `start ↦ stop` and `stop ↦ start`.  This is the
distance-preserving bijection used to place both orientations of a chunk
system onto the copies of the level step. -/

/-- Unfold the two-copy chain distance to the binary glue distance. -/
theorem chain2_dist_def {X : Type*} [MetricSpace X] (s t : X)
    (p q : Chain2Point X s t) :
    letI := chain2Metric X s t
    dist p q = glueDist t s p q := rfl

/-- Unfold the three-copy chain distance to the iterated glue distance. -/
theorem chain3_dist_def {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)
    (p q : Chain3Point X s t) :
    letI := chain3Metric X s t hst
    dist p q =
      (letI := chain2Metric X s t
       glueDist (Sum.inr (⟨t, hst.symm⟩ : GluePoint X s)) s p q) := rfl

namespace Chain3

variable {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t)

open Classical in
/-- Reversal of the three-copy path: copy `i` of the `(s,t)`-chain maps to
copy `2-i` of the `(t,s)`-chain, junction representatives to junction
representatives. -/
noncomputable def rev : Chain3Point X s t → Chain3Point X t s
  | Sum.inl (Sum.inl x) =>
      if h : x = t then Sum.inl (Sum.inr ⟨s, hst⟩)
      else Sum.inr ⟨x, h⟩
  | Sum.inl (Sum.inr x) =>
      if h : x.1 = t then Sum.inl (Sum.inl s)
      else Sum.inl (Sum.inr ⟨x.1, h⟩)
  | Sum.inr x => Sum.inl (Sum.inl x.1)

/-- Reversing twice is the identity. -/
theorem rev_rev (p : Chain3Point X s t) :
    rev t s hst.symm (rev s t hst p) = p := by
  rcases p with (x | x) | x
  · by_cases hx : x = t
    · subst hx
      simp [rev]
    · simp [rev, hx]
  · by_cases hx : x.1 = t
    · simp [rev, hx]
      exact Subtype.ext hx.symm
    · simp [rev, hx, x.2]
  · simp [rev, x.2]

/-- The reversal as a bijection. -/
noncomputable def revEquiv : Chain3Point X s t ≃ Chain3Point X t s where
  toFun := rev s t hst
  invFun := rev t s hst.symm
  left_inv p := rev_rev s t hst p
  right_inv p := rev_rev t s hst.symm p

/-- The reversal preserves distances. -/
theorem rev_dist (p q : Chain3Point X s t) :
    letI := chain3Metric X t s hst.symm
    letI := chain3Metric X s t hst
    dist (rev s t hst p) (rev s t hst q) = dist p q := by
  letI := chain3Metric X t s hst.symm
  letI := chain3Metric X s t hst
  rcases p with (x | x) | x <;> rcases q with (y | y) | y
  · by_cases hx : x = t <;> by_cases hy : y = t <;>
      simp [rev, hx, hy, chain3_dist_def, chain2_dist_def, glueDist,
        dist_comm] <;> try ring
  · by_cases hx : x = t <;> by_cases hy : y.1 = t <;>
      simp [rev, hx, hy, chain3_dist_def, chain2_dist_def, glueDist,
        dist_comm] <;> try ring
  · by_cases hx : x = t <;>
      simp [rev, hx, chain3_dist_def, chain2_dist_def, glueDist,
        dist_comm] <;> try ring
  · by_cases hx : x.1 = t <;> by_cases hy : y = t <;>
      simp [rev, hx, hy, chain3_dist_def, chain2_dist_def, glueDist,
        dist_comm] <;> try ring
  · by_cases hx : x.1 = t <;> by_cases hy : y.1 = t <;>
      simp [rev, hx, hy, chain3_dist_def, chain2_dist_def, glueDist,
        dist_comm] <;> try ring
  · by_cases hx : x.1 = t <;>
      simp [rev, hx, chain3_dist_def, chain2_dist_def, glueDist,
        dist_comm] <;> try ring
  · by_cases hy : y = t <;>
      simp [rev, hy, chain3_dist_def, chain2_dist_def, glueDist,
        dist_comm] <;> try ring
  · by_cases hy : y.1 = t <;>
      simp [rev, hy, chain3_dist_def, chain2_dist_def, glueDist,
        dist_comm] <;> try ring
  · simp [rev, chain3_dist_def, chain2_dist_def, glueDist, dist_comm]

/-- The reversal maps `start` to `stop`. -/
theorem rev_start : rev s t hst (start s t) = stop t s hst.symm := by
  show rev s t hst (Sum.inl (Sum.inl s)) = _
  rw [rev, dif_neg hst]
  rfl

/-- The reversal maps `stop` to `start`. -/
theorem rev_stop : rev s t hst (stop s t hst) = start t s := rfl

/-- The reversal bijection preserves distances (interface form for
chunk-system transport). -/
theorem revEquiv_dist (p q : Chain3Point X s t) :
    letI := chain3Metric X t s hst.symm
    letI := chain3Metric X s t hst
    dist (revEquiv s t hst p) (revEquiv s t hst q) = dist p q :=
  rev_dist s t hst p q

end Chain3

end KServer


