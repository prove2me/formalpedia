-- Prove2me | solution 2 for FreeMonoidShuffle.unsh_coassoc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:11:03.228351+00:00
-- url     : https://prove2.me/submissions/d1fa0cf9-e3aa-480f-ad4e-1f426f4ae9f2

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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FMS

theorem unsh_nil : unsh ([] : List X) = {([], [])} := rfl

theorem unsh_cons (a : X) (w : List X) :
    unsh (a :: w)
      = ((unsh w).map (fun p => (a :: p.1, p.2))) + ((unsh w).map (fun p => (p.1, a :: p.2))) :=
  rfl

theorem unsh_coassoc (w : List X) : coL w = coR w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hL : coL (a :: w)
        = ((coL w).map (fun t : List X × List X × List X => (a :: t.1, t.2.1, t.2.2))
            + (coL w).map (fun t : List X × List X × List X => (t.1, a :: t.2.1, t.2.2)))
          + (coL w).map (fun t : List X × List X × List X => (t.1, t.2.1, a :: t.2.2)) := by
      simp only [coL, unsh_cons, Multiset.add_bind, Multiset.bind_map, Multiset.map_bind,
        Multiset.map_add, Multiset.bind_add, Multiset.map_map, Function.comp_def]
    have hR : coR (a :: w)
        = (coR w).map (fun t : List X × List X × List X => (a :: t.1, t.2.1, t.2.2))
          + ((coR w).map (fun t : List X × List X × List X => (t.1, a :: t.2.1, t.2.2))
            + (coR w).map (fun t : List X × List X × List X => (t.1, t.2.1, a :: t.2.2))) := by
      simp only [coR, unsh_cons, Multiset.add_bind, Multiset.bind_map, Multiset.map_bind,
        Multiset.map_add, Multiset.bind_add, Multiset.map_map, Function.comp_def]
    rw [hL, hR, ih, add_assoc]

/-! ### The exponential of a plane is a shuffle character -/

end FMS

theorem solution (w : List X) : coL w = coR w :=
  FMS.unsh_coassoc w
