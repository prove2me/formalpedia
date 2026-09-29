-- Prove2me | Theorems.Thm_ShuffleOfSeries_isRepresentative_shuffleSeries
-- name    : ShuffleOfSeries.isRepresentative_shuffleSeries
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:30:40.844987+00:00
-- url     : https://prove2.me/theorems/d3a2ed81-0aa3-4d9d-aa80-d9869ea12f0c
-- title:
--   The shuffle product of two representative functions is representative.
-- statement:
--   **The shuffle product of two representative functions is representative.**  Together
--   with `RepresentativeFunctions.isRepresentative_mul` (Hadamard product) and
--   `isRepresentative_add`, this makes the representative functions a subalgebra of `K^{X*}`
--   for both products.
--
--   ```lean
--   theorem ShuffleOfSeries.isRepresentative_shuffleSeries{f g : List X → K} (hf : IsRepresentative f)
--       (hg : IsRepresentative g) : IsRepresentative (shuffleSeries f g) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShuffleOfSeries.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShuffleOfSeries.lean#L138

-- Thm stub generated from Novelty/ShuffleOfSeries.lean
import Mathlib
import Definitions.Def_Novelty_FreeMonoidCharacters
import Definitions.Def_Novelty_RepresentativeFunctions
import Definitions.Def_Novelty_ShuffleOfSeries
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

open ShuffleOfSeries

open RepresentativeFunctions FreeMonoidShuffle

variable {X K : Type*} [Field K]

/-! ## Auxiliary sum manipulations -/




/-! ## The shuffle product of series -/





/-! ## Associativity, from coassociativity of the unshuffle coproduct -/




/-! ## Rationality is preserved by the shuffle product -/

theorem ShuffleOfSeries.isRepresentative_shuffleSeries{f g : List X → K} (hf : IsRepresentative f)
    (hg : IsRepresentative g) : IsRepresentative (shuffleSeries f g) := by sorry
