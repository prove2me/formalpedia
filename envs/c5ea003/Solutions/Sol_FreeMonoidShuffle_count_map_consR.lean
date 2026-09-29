-- Prove2me | solution 1 for FreeMonoidShuffle.count_map_consR
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:59:06.591536+00:00
-- url     : https://prove2.me/submissions/d5607080-90b4-4c54-9727-0d86496a73b7

-- Sol generated from Novelty/FreeMonoidUnshuffle.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
/-
# The unshuffle coproduct and shuffle/unshuffle duality

Continuation of `Novelty.FreeMonoidShuffle`.  We introduce the *unshuffle* coproduct

`Δ_⧢ (w) = Σ_{w = u ⧢ v} u ⊗ v`

defined by the recursion `Δ_⧢(a·w) = (a ⊗ 1 + 1 ⊗ a) · Δ_⧢(w)` (the unique
concatenation-algebra morphism making every letter primitive), and prove:

* `count_shuf_eq_count_unsh` : **duality** — the multiplicity of `w` in the shuffle
  `u ⧢ v` equals the multiplicity of `(u,v)` in the unshuffle of `w`.  This is the
  statement that the shuffle product and the unshuffle coproduct are transposes of one
  another for the canonical pairing on words.
* `unsh_append` : the unshuffle coproduct is multiplicative for concatenation
  (the bialgebra axiom for `(K⟨X⟩, concatenation, Δ_⧢)`).
* `unsh_coassoc` : the unshuffle coproduct is coassociative.
* `unsh_card`, `unsh_length_mem` : grading data.
-/

open FreeMonoidShuffle

variable {X : Type*}

/-! ## The unshuffle coproduct -/






/-! ## Counting lemmas -/

variable [DecidableEq X]








/-! ## The unshuffle coproduct is an algebra morphism for concatenation -/





/-! ## Coassociativity -/






/-! ## Cocommutativity -/



open FreeMonoidShuffle in
theorem solution(a c : X) (u v : List X) (s : Multiset (List X × List X)) :
    Multiset.count (u, c :: v) (s.map (fun q => (q.1, a :: q.2))) =
      if a = c then Multiset.count (u, v) s else 0 := by
  by_cases h : a = c
  · subst h
    rw [if_pos rfl]
    have : ((u, a :: v) : List X × List X) = (fun q : List X × List X => (q.1, a :: q.2)) (u, v) :=
      rfl
    rw [this]
    exact Multiset.count_map_eq_count' _ _ (fun x y hxy => by
      simp only [Prod.mk.injEq, List.cons.injEq] at hxy
      exact Prod.ext hxy.1 hxy.2.2) _
  · rw [if_neg h]
    refine Multiset.count_eq_zero_of_notMem ?_
    intro hmem
    obtain ⟨y, _, hy⟩ := Multiset.mem_map.1 hmem
    simp only [Prod.mk.injEq, List.cons.injEq] at hy
    exact h hy.2.1
