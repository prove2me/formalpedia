-- Prove2me | Definitions.Def_Novelty_ShuffleOfSeries
-- name    : Novelty_ShuffleOfSeries
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:40.212438+00:00
-- url     : https://prove2.me/theorems/5da6f4a2-f606-4ce9-8589-c6c9a0510a02
-- title:
--   Aether Catalog definitions — Novelty_ShuffleOfSeries
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ShuffleOfSeries`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ShuffleOfSeries.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_FreeMonoidCharacters
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Definitions.Def_Novelty_RepresentativeFunctions
/-
# The shuffle product of series and rationality

The shuffle product of two noncommutative series is defined coefficientwise through the
unshuffle coproduct:

`(S ⧢ T | w) = Σ_{(u,v) ∈ Δ_⧢(w)} (S|u) (T|v)`.

This file proves:

* `shuffleSeries_delta` : the shuffle product of series extends the shuffle product of
  words — the shuffle of the two "Dirac" series at `u` and `v` is the series whose
  coefficient at `w` is the multiplicity of `w` in `u ⧢ v`.  This is exactly the duality
  `count_shuf_eq_count_unsh` of `Novelty.FreeMonoidUnshuffle` in action.
* `shuffleSeries_comm` : the shuffle product of series is commutative (from the
  cocommutativity of the unshuffle coproduct).
* `shuffleSeries_counit_left`, `shuffleSeries_assoc` : the counit is a unit and the
  product is associative (from coassociativity `unsh_coassoc`), so the series form a
  commutative monoid for the shuffle product.
* `isRepresentative_shuffleSeries` : **the shuffle product of two representative
  functions is representative** — the rational (Kleene–Schützenberger) series form a
  subalgebra for the shuffle product as well as for the Hadamard product.  The proof is a
  direct consequence of the bialgebra axiom `unsh_append`: the factorization of `S ⧢ T` is
  obtained by shuffling the factorizations of `S` and of `T`.
-/

namespace ShuffleOfSeries

open RepresentativeFunctions FreeMonoidShuffle

variable {X K : Type*} [Field K]

/-! ## Auxiliary sum manipulations -/




/-! ## The shuffle product of series -/

/-- The shuffle product of two series, defined coefficientwise by the unshuffle
coproduct. -/
def shuffleSeries (f g : List X → K) : List X → K :=
  fun w => ((unsh w).map (fun p => f p.1 * g p.2)).sum




/-! ## Associativity, from coassociativity of the unshuffle coproduct -/




/-! ## Rationality is preserved by the shuffle product -/


end ShuffleOfSeries


