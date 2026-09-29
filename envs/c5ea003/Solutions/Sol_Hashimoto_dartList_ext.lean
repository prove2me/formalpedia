-- Prove2me | solution 1 for Hashimoto.dartList_ext
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:41:22.472979+00:00
-- url     : https://prove2.me/submissions/765229a1-fe0c-4ffe-be2b-a929d7d9e3a2

-- Sol generated from Algebra/NonBacktracking/VertexCycles.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_VertexCycles

/-!
# The vertex form of the non-backtracking trace formula

`Hashimoto.trace_hashimoto_pow` counts rooted closed non-backtracking walks as lists of
*darts*.  Classically one prefers the *vertex* description: a rooted closed
non-backtracking walk of length `n` is a cyclic word `u₀ u₁ … u_{n-1}` of vertices with

* `uᵢ` adjacent to `u_{i+1}` for all `i` **cyclically**, and
* `u_{i+2} ≠ uᵢ` for all `i` **cyclically** (no immediate backtracking, including across
  the seam).

Cyclic conditions are expressed with `List.rotate`: "`∀ i, R uᵢ u_{i+1 mod n}`" is exactly
`List.Forall₂ R u (u.rotate 1)`.

## Main results

* `Hashimoto.isChain_seam_iff_forall₂_rotate` — a list is a chain *and* closes up under
  the relation iff it is `Forall₂`-related to its own rotation. This converts the linear
  (chain) description of closed walks into the genuinely cyclic one.
* `Hashimoto.mem_cyclicNBVertexSeqs` — the vertex description above really describes the
  image of the dart cycles under `d ↦ d.fst`.
* `Hashimoto.trace_hashimoto_pow_eq_card_cyclicNBVertexSeqs` —
  `trace (B ^ n) = #{cyclically non-backtracking closed vertex words of length n}`
  for `n ≥ 1`.
-/

open Finset RelWalkCount SimpleGraph List

open Hashimoto

/-! ## List lemmas -/


variable {α β γ γ' : Type*}







/-! ## Cyclic dart words -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable {G}



variable (G)

/-! ## Cyclic vertex words -/


variable {G}




variable (G)



open Hashimoto in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem solution: ∀ {c c' : List G.Dart},
    c.map (fun d => d.toProd.1) = c'.map (fun d => d.toProd.1) →
    c.map (fun d => d.toProd.2) = c'.map (fun d => d.toProd.2) → c = c' := by
  intro c
  induction c with
  | nil =>
      intro c' h1 _
      cases c' with
      | nil => rfl
      | cons d t => simp at h1
  | cons d t ih =>
      intro c' h1 h2
      cases c' with
      | nil => simp at h1
      | cons d' t' =>
          simp only [List.map_cons, List.cons.injEq] at h1 h2
          rw [ih h1.2 h2.2]
          exact congrArg (· :: t') (SimpleGraph.Dart.ext _ _ (Prod.ext h1.1 h2.1))
