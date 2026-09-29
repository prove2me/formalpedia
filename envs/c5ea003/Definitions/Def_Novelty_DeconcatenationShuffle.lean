-- Prove2me | Definitions.Def_Novelty_DeconcatenationShuffle
-- name    : Novelty_DeconcatenationShuffle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:14:28.440603+00:00
-- url     : https://prove2.me/theorems/193b22f2-291e-4932-ac4d-151e7690c052
-- title:
--   Aether Catalog definitions — Novelty_DeconcatenationShuffle
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.DeconcatenationShuffle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/DeconcatenationShuffle.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
/-
# The deconcatenation coproduct and the shuffle bialgebra

This file completes the picture of `Novelty.FreeMonoidUnshuffle` by treating the *other*
of the two mutually dual bialgebra structures on `K⟨X⟩`:

* `(K⟨X⟩, concatenation, Δ_⧢)` — the graded noncommutative co-commutative bialgebra,
  handled in `Novelty.FreeMonoidUnshuffle` (`unsh_append`, `unsh_coassoc`);
* `(K⟨X⟩, ⧢, Δ_conc)` — the commutative, co-noncommutative bialgebra of this file,
  where `Δ_conc(w) = Σ_{w = z₁z₂} z₁ ⊗ z₂` is the deconcatenation coproduct.

The main theorem `deconc_bind_shuf` is the bialgebra axiom for the second structure:
deconcatenation is an algebra morphism for the shuffle product,

`Δ_conc(u ⧢ v) = Δ_conc(u) ⧢₂ Δ_conc(v)`,

where `⧢₂` is the shuffle product of the tensor square.  The proof is *by duality*: both
sides are computed coefficientwise, the coefficients are transported to the unshuffle
side through `count_shuf_eq_count_unsh`, and there they become the multiplicativity of
the unshuffle coproduct `unsh_append`, up to a purely combinatorial four-fold
transposition of counting sums (`quad_transpose`).
-/

namespace FreeMonoidShuffle

variable {X : Type*}

/-! ## Elementary counting lemmas -/

section CountingLemmas
variable {A B C D : Type*}







end CountingLemmas

/-! ## The deconcatenation coproduct -/

/-- The deconcatenation coproduct `Δ_conc(w) = Σ_{w = z₁z₂} z₁ ⊗ z₂`. -/
def deconc : List X → Multiset (List X × List X)
  | [] => {([], [])}
  | a :: w => (([], a :: w) : List X × List X) ::ₘ ((deconc w).map (fun p => (a :: p.1, p.2)))





/-! ## The shuffle product of the tensor square -/

/-- Shuffle product of two elementary tensors of words. -/
def shufPair (p q : List X × List X) : Multiset (List X × List X) :=
  (shuf p.1 q.1).bind (fun r => (shuf p.2 q.2).map (fun s => (r, s)))

/-- `Δ_conc(u) ⧢₂ Δ_conc(v)`, the shuffle product on the tensor square applied to the two
deconcatenation coproducts. -/
def deconcShufProd (u v : List X) : Multiset (List X × List X) :=
  (deconc u).bind (fun p => (deconc v).bind (fun q => shufPair p q))


/-! ## The bialgebra axiom -/


end FreeMonoidShuffle


