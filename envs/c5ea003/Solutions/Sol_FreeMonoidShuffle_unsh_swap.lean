-- Prove2me | solution 1 for FreeMonoidShuffle.unsh_swap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:08:19.065359+00:00
-- url     : https://prove2.me/submissions/022c6d75-0f0a-447a-8832-c0ff6731611e

-- Sol generated from Novelty/FreeMonoidUnshuffle.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Theorems.Thm_FreeMonoidShuffle_unsh_cons
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
theorem solution(w : List X) : (unsh w).map Prod.swap = unsh w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [unsh_cons, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rw [show ((Prod.swap ∘ fun p : List X × List X => (a :: p.1, p.2))
        = (fun p : List X × List X => (p.1, a :: p.2)) ∘ Prod.swap) from rfl,
      show ((Prod.swap ∘ fun p : List X × List X => (p.1, a :: p.2))
        = (fun p : List X × List X => (a :: p.1, p.2)) ∘ Prod.swap) from rfl,
      ← Multiset.map_map, ← Multiset.map_map, ih]
    exact add_comm _ _
