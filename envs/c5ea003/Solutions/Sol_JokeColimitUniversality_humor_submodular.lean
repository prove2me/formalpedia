-- Prove2me | solution 1 for JokeColimitUniversality.humor_submodular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:35:29.024721+00:00
-- url     : https://prove2.me/submissions/964ff00d-abaa-4d4a-812b-a8565392a1ce

-- Sol generated from Applications/JokeColimitUniversality.lean
import Mathlib
import Definitions.Def_Applications_JokeColimitUniversality
import Definitions.Def_Applications_JokeSurpriseAlgebra

/-!
# Humor is a colimit: universality, submodularity, and the failure of expected resolutions

This file continues the programme begun in `Applications.JokeSurpriseAlgebra`, where a
*setup* was modelled by a nonempty finite configuration of resolutions `S ⊆ ℝ` and its
*surprise* by the range `humor S = max' S - min' S`. There, surprise was shown to be a
monotone functor on the refinement poset, subadditive under shared context.

Here we push the categorical slogan of the programme — **"the punchline is a colimit,
the expected resolution is a limit"** — to its logical conclusion, and we test the
associated universality conjecture ("the funniest jokes are the terminal ones").

## Results

### The exact combination law
* `humor_submodular` : surprise is a **submodular valuation**:
  `humor (S ∪ T) + humor (S ∩ T) ≤ humor S + humor T` whenever the two setups share a
  reading. This *strictly strengthens* the catalog's `humor_union_le_add_of_inter`,
  which is recovered as `humor_union_le_add_of_inter_of_submodular`.
* `humor_inter_le_union` : the colimit (joint reading) is always at least as surprising
  as the limit (shared reading).

### Colimits exist, limits need not
* `jointIsColimit` : the joint setup `S ∪ T` **is** the binary coproduct of `S` and `T`
  in the category of setups; so every pair of jokes has a colimit.
* `no_binaryProduct_of_disjoint` : two setups with no shared reading have **no** binary
  product. The expected resolution — the limit — genuinely may fail to exist, while the
  punchline — the colimit — always does. This is the precise sense in which humor is a
  colimit.

### Universality
* `le_obj_of_isTerminal` : for *any* category `C` and *any* real-valued functor
  `F : C ⥤ ℝ`, a terminal object maximises `F`. Terminality is therefore a purely
  categorical certificate of maximal surprise.
* `JokeOver` : the category of jokes with a fixed setup `S`, bounded by an ambient
  universe `U`; `isTerminal_ambient` shows the ambient universe is its terminal object, and
  `humor_le_of_isTerminal` shows universal jokes are the funniest ones.
* `humor_eq_of_isTerminal` : any two universal jokes over the same setup have exactly
  the same surprise — the humor of a universal joke is a well-defined invariant.

### Where the conjecture breaks
* `humor_not_reflects_refinement` : surprise does **not** reflect the order. There are
  strictly refining setups of identical surprise, so maximal surprise does *not* imply
  terminality.
* `exists_maximal_humor_not_terminal` : consequently there is a joke category with a
  non-terminal object of maximal humor. The implication "universal ⇒ funniest" is a
  theorem; its converse "funniest ⇒ universal" is **false**.

-- !-- Lab Notes -- !--
Hypothesis (H1): surprise is not merely subadditive under shared context, but exactly
submodular — the union/intersection defect is controlled by the four extremes.
Hypothesis (H2): the slogan "humor is a colimit" is literally true: the category of
setups has all binary coproducts but not all binary products.
Hypothesis (H3): "funniest = universal = terminal" is an equivalence.

Experiment: H1 was reduced to the four inequalities
`min' S ≤ min' (S ∩ T) ≤ max' (S ∩ T) ≤ max' S` (and the same for `T`) plus the
identity `max (A,B) + min (A,B) = A + B`, discharged by `split_ifs <;> linarith` after
`max_def`/`min_def`. H2 was proved by exhibiting the colimit cocone explicitly
(`BinaryCofan.IsColimit.mk`, all coherence conditions free by thinness) and by deriving
a contradiction from `prod.fst`/`prod.snd` for disjoint setups. H3 was tested on the
pair `{0,1} ⊂ {0,1/2,1}`.

Analysis: H1 and H2 survive. H3 is **false**, and the failure is structural rather
than accidental: surprise only sees the two extremal readings, so it is blind to every
refinement that adds interior readings. Terminality implies maximal surprise
(`humor_le_of_isTerminal`), but maximal surprise is attained on a whole up-set of
non-terminal objects. The correct guarded statement is: universal jokes maximise
surprise, and all universal jokes over a fixed setup are equally surprising.

Critique: `no_binaryProduct_of_disjoint` needs disjointness, not merely distinctness —
with a shared reading the intersection *is* the product. The counterexample to H3 uses
a genuinely strict refinement (`{0,1} ⊊ {0,1/2,1}`), so it is not an artefact of a
degenerate category.

Synthesis: colimits are unconditional and limits are conditional; universality is a
sufficient but not necessary condition for maximal humor; and surprise is an exactly
submodular valuation on the refinement lattice.
-/

open CategoryTheory Limits Finset JokeSurpriseAlgebra

open JokeColimitUniversality

/-! ### The exact combination law -/





/-! ### Colimits always exist -/






/-! ### Universality: terminal objects maximise every invariant -/












/-! ### The converse fails -/










open JokeColimitUniversality in
theorem solution(S T : Finset ℝ) (hS : S.Nonempty) (hT : T.Nonempty)
    (h : (S ∩ T).Nonempty) :
    humor (S ∪ T) hS.inl + humor (S ∩ T) h ≤ humor S hS + humor T hT := by
  have h1 : (S ∩ T).max' h ≤ S.max' hS :=
    S.le_max' _ (Finset.mem_of_mem_inter_left ((S ∩ T).max'_mem h))
  have h2 : (S ∩ T).max' h ≤ T.max' hT :=
    T.le_max' _ (Finset.mem_of_mem_inter_right ((S ∩ T).max'_mem h))
  have h3 : S.min' hS ≤ (S ∩ T).min' h :=
    S.min'_le _ (Finset.mem_of_mem_inter_left ((S ∩ T).min'_mem h))
  have h4 : T.min' hT ≤ (S ∩ T).min' h :=
    T.min'_le _ (Finset.mem_of_mem_inter_right ((S ∩ T).min'_mem h))
  unfold humor
  rw [Finset.max'_union hS hT, Finset.min'_union hS hT]
  simp only [max_def, min_def]
  split_ifs <;> linarith
