-- Prove2me | solution 3 for FreeMonoidShuffle.unsh_swap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:10:59.087105+00:00
-- url     : https://prove2.me/submissions/c2232b2d-9954-41d1-b14f-51174a62b937

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





/-! ## Coassociativity -/






/-! ## Cocommutativity -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FMS

theorem unsh_cons (a : X) (w : List X) :
    unsh (a :: w)
      = ((unsh w).map (fun p => (a :: p.1, p.2))) + ((unsh w).map (fun p => (p.1, a :: p.2))) :=
  rfl

theorem unsh_swap (w : List X) : (unsh w).map Prod.swap = unsh w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have h1 : (Prod.swap ∘ fun p : List X × List X => (a :: p.1, p.2))
        = (fun p : List X × List X => (p.1, a :: p.2)) ∘ Prod.swap := rfl
    have h2 : (Prod.swap ∘ fun p : List X × List X => (p.1, a :: p.2))
        = (fun p : List X × List X => (a :: p.1, p.2)) ∘ Prod.swap := rfl
    rw [unsh_cons, Multiset.map_add, Multiset.map_map, Multiset.map_map, h1, h2,
      ← Multiset.map_map, ← Multiset.map_map, ih]
    exact add_comm _ _

/-! ### The unshuffle coproduct is a concatenation morphism -/

end FMS

theorem solution (w : List X) : (unsh w).map Prod.swap = unsh w :=
  FMS.unsh_swap w
