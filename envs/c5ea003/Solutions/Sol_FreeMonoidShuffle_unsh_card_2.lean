-- Prove2me | solution 2 for FreeMonoidShuffle.unsh_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:10:57.29142+00:00
-- url     : https://prove2.me/submissions/0775788c-77e8-4313-be97-4e9f1a78d1b1

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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FMS

theorem unsh_cons (a : X) (w : List X) :
    unsh (a :: w)
      = ((unsh w).map (fun p => (a :: p.1, p.2))) + ((unsh w).map (fun p => (p.1, a :: p.2))) :=
  rfl

theorem unsh_card (w : List X) : (unsh w).card = 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [unsh_cons, Multiset.card_add, Multiset.card_map, Multiset.card_map, ih,
      List.length_cons, pow_succ]
    ring

end FMS

theorem solution (w : List X) : (unsh w).card = 2 ^ w.length :=
  FMS.unsh_card w
