-- Prove2me | solution 1 for Hashimoto.isChain_seam_iff_forall2_rotate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T20:28:21.354321+00:00
-- url     : https://prove2.me/submissions/ff3ecc7b-4564-414a-8ff3-68207329516a

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




/-- Auxiliary form of the cyclic-chain criterion with an explicit closing element. -/
private lemma isChain_append_singleton_iff {R : α → α → Prop} :
    ∀ (t : List α) (x z : α),
      (IsChain R (x :: t) ∧ ∀ w ∈ (x :: t).getLast?, R w z) ↔ Forall₂ R (x :: t) (t ++ [z]) := by
  intro t
  induction t with
  | nil =>
      intro x z
      simp [List.forall₂_cons]
  | cons y s ih =>
      intro x z
      rw [List.cons_append, List.forall₂_cons, ← ih y z]
      simp only [List.isChain_cons_cons, List.getLast?_cons_cons]
      tauto



/-! ## Cyclic dart words -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable {G}



variable (G)

/-! ## Cyclic vertex words -/


variable {G}




variable (G)



open Hashimoto in
theorem solution{R : α → α → Prop} {l : List α} (hne : l ≠ []) :
    (IsChain R l ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y) ↔ Forall₂ R l (l.rotate 1) := by
  match l, hne with
  | x :: t, _ =>
      rw [List.rotate_cons_succ, List.rotate_zero, ← isChain_append_singleton_iff t x x]
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq]
      constructor
      · rintro ⟨hchain, hseam⟩
        exact ⟨hchain, fun w hw => hseam w hw x rfl⟩
      · rintro ⟨hchain, hseam⟩
        refine ⟨hchain, fun w hw y hy => ?_⟩
        subst hy
        exact hseam w hw
