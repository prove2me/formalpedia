-- Prove2me | Definitions.Def_Applications_JokeColimitUniversality
-- name    : Applications_JokeColimitUniversality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:49:03.619014+00:00
-- url     : https://prove2.me/theorems/56256270-22e2-4816-b463-b5e3ec1257c7
-- title:
--   Aether Catalog definitions — Applications_JokeColimitUniversality
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.JokeColimitUniversality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/JokeColimitUniversality.lean by skeleton subtraction
import Mathlib
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

namespace JokeColimitUniversality

/-! ### The exact combination law -/





/-! ### Colimits always exist -/

/-- The **joint setup**: telling both jokes at once. -/
noncomputable def joint (S T : Setup) : Setup := ⟨S.1 ∪ T.1, S.2.inl⟩

/-- The cocone exhibiting the joint setup as a candidate coproduct. -/
noncomputable def cofanJoint (S T : Setup) : BinaryCofan S T :=
  BinaryCofan.mk (P := joint S T) (homOfLE Finset.subset_union_left)
    (homOfLE Finset.subset_union_right)

/-- **The punchline is a colimit.** The joint setup `S ∪ T` is the binary coproduct of
`S` and `T` in the category of setups. -/
noncomputable def jointIsColimit (S T : Setup) : IsColimit (cofanJoint S T) :=
  BinaryCofan.IsColimit.mk _
    (fun {_} f g => homOfLE (Finset.union_subset (leOfHom f) (leOfHom g)))
    (fun _ _ => Subsingleton.elim _ _) (fun _ _ => Subsingleton.elim _ _)
    (fun _ _ _ _ _ => Subsingleton.elim _ _)



/-! ### Universality: terminal objects maximise every invariant -/



/-- The **category of jokes over a setup** `S`, inside an ambient universe `U` of
readings: an object is a setup refining `S` and contained in `U`, and a morphism is a
refinement. -/
def JokeOver (S U : Setup) : Type := {T : Setup // S ≤ T ∧ T ≤ U}

instance (S U : Setup) : Preorder (JokeOver S U) := Subtype.preorder _

/-- The ambient universe of readings, viewed as a joke over `S`. -/
def ambient (S U : Setup) (h : S ≤ U) : JokeOver S U := ⟨U, h, le_refl U⟩


/-- Surprise, as an invariant of jokes over a fixed setup. -/
noncomputable def humorOver {S U : Setup} (J : JokeOver S U) : ℝ := humorS J.1

theorem humorOver_monotone {S U : Setup} : Monotone (humorOver (S := S) (U := U)) :=
  fun _ _ h => humorS_monotone h

/-- Surprise as a functor on the category of jokes over a fixed setup. -/
noncomputable def humorOverFunctor (S U : Setup) : JokeOver S U ⥤ ℝ :=
  (humorOver_monotone (S := S) (U := U)).functor



/-! ### The converse fails -/


/-- The two-reading setup `{0, 1}`. -/
noncomputable def pun : Setup := ⟨{0, 1}, ⟨0, by simp⟩⟩

/-- Its refinement by an intermediate reading, `{0, 1/2, 1}`. -/
noncomputable def punRefined : Setup := ⟨{0, 1/2, 1}, ⟨0, by simp⟩⟩






end JokeColimitUniversality


