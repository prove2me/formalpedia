-- Prove2me | solution 2 for FreeMonoidShuffle.unsh_append
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:11:01.088094+00:00
-- url     : https://prove2.me/submissions/f95e1511-e40e-41c1-ab49-7e159501b272

-- Thm stub generated from Novelty/FreeMonoidUnshuffle.lean
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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FMS

theorem unsh_nil : unsh ([] : List X) = {([], [])} := rfl

theorem unsh_cons (a : X) (w : List X) :
    unsh (a :: w)
      = ((unsh w).map (fun p => (a :: p.1, p.2))) + ((unsh w).map (fun p => (p.1, a :: p.2))) :=
  rfl

theorem unsh_append (u v : List X) : unsh (u ++ v) = pairMul (unsh u) (unsh v) := by
  induction u with
  | nil =>
    simp only [List.nil_append, unsh_nil, pairMul, Multiset.singleton_bind, List.nil_append]
    simp
  | cons a u ih =>
    rw [List.cons_append, unsh_cons, ih, unsh_cons]
    simp only [pairMul, Multiset.add_bind, Multiset.bind_map, Multiset.map_bind, Multiset.map_map,
      Function.comp_def, List.cons_append]

/-! ### Multiplicativity along shuffles -/

end FMS

theorem solution (u v : List X) : unsh (u ++ v) = pairMul (unsh u) (unsh v) :=
  FMS.unsh_append u v
