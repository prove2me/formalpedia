-- Prove2me | Definitions.Def_Novelty_FreeMonoidUnshuffle
-- name    : Novelty_FreeMonoidUnshuffle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:13:38.62654+00:00
-- url     : https://prove2.me/theorems/d0036195-93b7-41ff-940b-26f7cac8be35
-- title:
--   Aether Catalog definitions — Novelty_FreeMonoidUnshuffle
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FreeMonoidUnshuffle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FreeMonoidUnshuffle.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
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

namespace FreeMonoidShuffle

variable {X : Type*}

/-! ## The unshuffle coproduct -/

/-- The unshuffle coproduct of a word: the multiset of all pairs `(u,v)` obtained by
splitting the positions of `w` into two complementary sets. -/
def unsh : List X → Multiset (List X × List X)
  | [] => {([], [])}
  | a :: w => ((unsh w).map (fun p => (a :: p.1, p.2))) + ((unsh w).map (fun p => (p.1, a :: p.2)))





/-! ## Counting lemmas -/

section Count
variable [DecidableEq X]







end Count

/-! ## The unshuffle coproduct is an algebra morphism for concatenation -/

/-- Componentwise concatenation of two multisets of pairs of words: the product of the
tensor square of `K⟨X⟩` for the concatenation product. -/
def pairMul (s t : Multiset (List X × List X)) : Multiset (List X × List X) :=
  s.bind (fun p => t.map (fun q => (p.1 ++ q.1, p.2 ++ q.2)))




/-! ## Coassociativity -/

/-- Left iterate of the unshuffle coproduct: `(Δ ⊗ id) ∘ Δ`. -/
def coL (w : List X) : Multiset (List X × List X × List X) :=
  (unsh w).bind (fun p => (unsh p.1).map (fun r => (r.1, r.2, p.2)))

/-- Right iterate of the unshuffle coproduct: `(id ⊗ Δ) ∘ Δ`. -/
def coR (w : List X) : Multiset (List X × List X × List X) :=
  (unsh w).bind (fun p => (unsh p.2).map (fun r => (p.1, r.1, r.2)))




/-! ## Cocommutativity -/


end FreeMonoidShuffle


