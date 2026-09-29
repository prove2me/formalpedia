-- Prove2me | Definitions.Def_Applications_JokeHullQuotient
-- name    : Applications_JokeHullQuotient
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:50:16.350274+00:00
-- url     : https://prove2.me/theorems/9b7e21df-4f38-4f2b-b655-c7150a8603ac
-- title:
--   Aether Catalog definitions — Applications_JokeHullQuotient
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.JokeHullQuotient`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/JokeHullQuotient.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_JokeColimitUniversality
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

namespace JokeHullQuotient

/-- An **interpretive interval**: the pair of extreme readings of a setup. -/
def Hull : Type := {p : ℝ × ℝ // p.1 ≤ p.2}

/-- Intervals are ordered by **inclusion**: a wider interval is larger. -/
instance : Preorder Hull where
  le p q := q.1.1 ≤ p.1.1 ∧ p.1.2 ≤ q.1.2
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨le_trans h₂.1 h₁.1, le_trans h₁.2 h₂.2⟩


/-- The **hull** of a setup: its two extreme readings. -/
noncomputable def hullOf (S : Setup) : Hull :=
  ⟨(S.1.min' S.2, S.1.max' S.2), S.1.min'_le_max' S.2⟩



/-- The surprise of an interpretive interval. -/
def humorHull (p : Hull) : ℝ := p.1.2 - p.1.1





/-! ### The repaired universality conjecture -/

variable {S U : Setup}

/-- A joke is **hull-universal** when its hull dominates that of every joke with the
same setup: it is a terminal object of the hull quotient of the joke category. -/
def HullTop (J : JokeOver S U) : Prop := ∀ K : JokeOver S U, hullOf K.1 ≤ hullOf J.1





end JokeHullQuotient


