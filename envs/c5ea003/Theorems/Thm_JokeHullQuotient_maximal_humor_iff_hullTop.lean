-- Prove2me | Theorems.Thm_JokeHullQuotient_maximal_humor_iff_hullTop
-- name    : JokeHullQuotient.maximal_humor_iff_hullTop
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:56:55.457316+00:00
-- url     : https://prove2.me/theorems/9e06bd11-0704-47f2-955e-e53b674a2332
-- title:
--   The universality conjecture, closed.
-- statement:
--   **The universality conjecture, closed.** For jokes over a fixed setup inside an
--   ambient universe `U`, a joke has maximal humor **iff** it is terminal in the hull
--   quotient. The counterexample of
--   `JokeColimitUniversality.exists_maximal_humor_not_terminal` is therefore precisely and
--   only the failure of the hull functor to be injective.
--
--   ```lean
--   theorem JokeHullQuotient.maximal_humor_iff_hullTop(h : S ≤ U) (J : JokeOver S U) :
--       (∀ K : JokeOver S U, humorOver K ≤ humorOver J) ↔ HullTop J := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/JokeHullQuotient.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/JokeHullQuotient.lean#L133

-- Thm stub generated from Applications/JokeHullQuotient.lean
import Mathlib
import Definitions.Def_Applications_JokeColimitUniversality
import Definitions.Def_Applications_JokeHullQuotient
import Definitions.Def_Applications_JokeSurpriseAlgebra

/-!
# Closing the universality conjecture: the hull quotient of the joke category

`Applications.JokeColimitUniversality` proved that universal (terminal) jokes maximise
surprise, and **refuted** the converse: `exists_maximal_humor_not_terminal` exhibits a
non-terminal joke of maximal humor, because a refinement that only adds *interior*
readings changes the joke without changing its surprise.

This file closes that open conjecture rather than abandoning it. The obstruction is
entirely accounted for by one construction: the **hull** of a setup, the pair of its
extreme readings. Surprise factors through the hull, the failure of the converse is
exactly the failure of the hull map to be injective, and after passing to the hull
quotient the conjecture becomes **true**.

## Results

* `hullFunctor` : the hull is a functor `Setup ⥤ Hull` from setups to interpretive
  intervals ordered by inclusion, and `humorS_eq_humorHull` shows surprise factors
  through it.
* `humorS_eq_iff_hull_eq` : **exactly what surprise reflects.** For a refinement
  `S ≤ T`, the surprises agree iff the hulls agree. Surprise is blind to interior
  readings and to nothing else.
* `maximal_humor_iff_hullTop` : **the repaired universality conjecture.** In the
  category of jokes over a fixed setup inside an ambient universe, a joke has maximal
  humor **iff** it is terminal in the hull quotient. "Funniest = universal" is true
  after localising at hull-equivalence, and false before (see
  `JokeColimitUniversality.exists_maximal_humor_not_terminal`).
* `hullTop_of_isTerminal` : terminality upstairs implies terminality downstairs, so
  the repaired statement is a genuine weakening of the original — the original
  implication is recovered as a corollary (`humor_le_of_hullTop`).

-- !-- Lab Notes -- !--
Hypothesis (H9): the counterexample to "funniest implies universal" is not a defect of
the humor invariant but an artefact of working in a category finer than the invariant
can see; localising at hull-equivalence should restore the equivalence.

Experiment: the hull map `S ↦ (min' S, max' S)` was made a functor into the poset of
intervals ordered by inclusion. The reflection lemma was reduced to the arithmetic
fact that if `m' ≤ m ≤ M ≤ M'` and `M - m = M' - m'` then `m = m'` and `M = M'`
(`linarith`). The repaired conjecture then follows in both directions from
monotonicity of `humorHull` and the reflection lemma.

Analysis: H9 survives in the strongest possible form — the criterion is an `iff`, not
an implication, and the hull quotient is the *coarsest* localisation that works, since
`humorS_eq_iff_hull_eq` shows any two setups identified by surprise along a refinement
already have equal hulls.

Critique: the localisation is not vacuous — the fibres of the hull map are large
(every interior reading may be added or removed freely), so the quotient genuinely
loses information about the joke while retaining exactly the information humor uses.
The result should therefore be read as a limitation of the humor invariant, not as a
vindication of the naive conjecture.

Synthesis: humor factors as `Setup ⥤ Hull ⥤ ℝ`; the first functor is where the
counterexample lives and the second is where the universality conjecture is true.
-/

open CategoryTheory Limits Finset JokeSurpriseAlgebra JokeColimitUniversality

open JokeHullQuotient












/-! ### The repaired universality conjecture -/

variable {S U : Setup}

theorem JokeHullQuotient.maximal_humor_iff_hullTop(h : S ≤ U) (J : JokeOver S U) :
    (∀ K : JokeOver S U, humorOver K ≤ humorOver J) ↔ HullTop J := by sorry
