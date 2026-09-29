-- Prove2me | Theorems.Thm_FreeMonoidShuffle_unsh_swap
-- name    : FreeMonoidShuffle.unsh_swap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:50:45.406658+00:00
-- url     : https://prove2.me/theorems/7b81934a-d814-4e9d-9b19-debca1164f13
-- title:
--   The unshuffle coproduct is cocommutative: this is the "co-commutative" half of the
-- statement:
--   **The unshuffle coproduct is cocommutative**: this is the "co-commutative" half of the
--   graded noncommutative co-commutative bialgebra `(K⟨X⟩, concatenation, Δ_⧢)`.
--
--   ```lean
--   theorem FreeMonoidShuffle.unsh_swap(w : List X) : (unsh w).map Prod.swap = unsh w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FreeMonoidUnshuffle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FreeMonoidUnshuffle.lean#L241

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

theorem FreeMonoidShuffle.unsh_swap(w : List X) : (unsh w).map Prod.swap = unsh w := by sorry
