-- Prove2me | solution 1 for Hashimoto.forall2_and_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T20:23:34.985377+00:00
-- url     : https://prove2.me/submissions/dd1d5369-5705-4ab5-b14e-adc07ecb89e9

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
theorem solution{R S : α → β → Prop} {l₁ : List α} {l₂ : List β} :
    Forall₂ (fun a b => R a b ∧ S a b) l₁ l₂ ↔ Forall₂ R l₁ l₂ ∧ Forall₂ S l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => simp
      | cons b t => simp
  | cons a s ih =>
      cases l₂ with
      | nil => simp
      | cons b t =>
          simp only [List.forall₂_cons, ih]
          tauto
