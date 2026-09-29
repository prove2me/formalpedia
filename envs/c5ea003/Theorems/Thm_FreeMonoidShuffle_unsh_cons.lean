-- Prove2me | Theorems.Thm_FreeMonoidShuffle_unsh_cons
-- name    : FreeMonoidShuffle.unsh_cons
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:50:00.67282+00:00
-- url     : https://prove2.me/theorems/14aba25e-86b3-4c8f-a1e1-f2af4c6f1154
-- title:
--   Unsh cons
-- statement:
--   Formal statement of `FreeMonoidShuffle.unsh_cons` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FreeMonoidShuffle.unsh_cons(a : X) (w : List X) :
--       unsh (a :: w) = ((unsh w).map (fun p => (a :: p.1, p.2))) +
--         ((unsh w).map (fun p => (p.1, a :: p.2))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FreeMonoidUnshuffle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FreeMonoidUnshuffle.lean#L35

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

theorem FreeMonoidShuffle.unsh_cons(a : X) (w : List X) :
    unsh (a :: w) = ((unsh w).map (fun p => (a :: p.1, p.2))) +
      ((unsh w).map (fun p => (p.1, a :: p.2))) := by sorry
