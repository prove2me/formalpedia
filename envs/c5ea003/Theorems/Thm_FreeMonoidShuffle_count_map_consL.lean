-- Prove2me | Theorems.Thm_FreeMonoidShuffle_count_map_consL
-- name    : FreeMonoidShuffle.count_map_consL
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:49:32.235567+00:00
-- url     : https://prove2.me/theorems/4e867aeb-01d2-488e-a637-8352d326521b
-- title:
--   Count map consL
-- statement:
--   Formal statement of `FreeMonoidShuffle.count_map_consL` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FreeMonoidShuffle.count_map_consL(a c : X) (u v : List X) (s : Multiset (List X × List X)) :
--       Multiset.count (c :: u, v) (s.map (fun q => (a :: q.1, q.2))) =
--         if a = c then Multiset.count (u, v) s else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FreeMonoidUnshuffle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FreeMonoidUnshuffle.lean#L74

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

theorem FreeMonoidShuffle.count_map_consL(a c : X) (u v : List X) (s : Multiset (List X × List X)) :
    Multiset.count (c :: u, v) (s.map (fun q => (a :: q.1, q.2))) =
      if a = c then Multiset.count (u, v) s else 0 := by sorry
