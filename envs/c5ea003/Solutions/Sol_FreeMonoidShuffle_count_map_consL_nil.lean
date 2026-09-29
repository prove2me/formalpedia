-- Prove2me | solution 1 for FreeMonoidShuffle.count_map_consL_nil
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:57:32.601361+00:00
-- url     : https://prove2.me/submissions/1741a6b9-124f-428f-99c4-c3aab3810c38

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
theorem solution(a : X) (v : List X) (s : Multiset (List X × List X)) :
    Multiset.count (([] : List X), v) (s.map (fun q => (a :: q.1, q.2))) = 0 := by
  refine Multiset.count_eq_zero_of_notMem ?_
  intro hmem
  obtain ⟨y, _, hy⟩ := Multiset.mem_map.1 hmem
  simp at hy
