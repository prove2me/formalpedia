-- Prove2me | solution 1 for HadwigerDebrunner.exists_transversal_of_pqProperty_full
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:00.945411+00:00
-- url     : https://prove2.me/submissions/8bc11590-752b-4d84-b477-9959b4d2769b

-- Sol generated from Geometry/HadwigerDebrunner/Combinatorial.lean
import Mathlib
import Definitions.Def_Geometry_HadwigerDebrunner_Combinatorial
/-
# Hadwiger–Debrunner `(p,q)`-property: the combinatorial core

This file develops the *set-class agnostic* combinatorial skeleton underlying the
Hadwiger–Debrunner `(p,q)` transversal theory.  Nothing here depends on convexity
or on a dimension: we work with an arbitrary finite family `F : ι → Set X`
indexed by a `Finset s`, and isolate exactly the combinatorial content of the
`(p,q)`-property and of *transversals* (piercing sets).

The two genuinely combinatorial facts proved here are:

* monotonicity of the `(p,q)`-property (strengthen `p`, weaken `q`); and
* the elementary transversal bound coming from the *full* `(|s|, q)`-property:
  if some `q` members share a point, that single point pierces all `q` of them,
  so the whole family is pierced by `|s| - q + 1` points.

These are the ingredients that are *independent of the Helly number*; the
Helly-number input (which is where dimension and the convex-vs-splinter
distinction enters, `d+1` vs `2d+1`) is supplied in `HellyBridge.lean`.

## Main results

* `HasPQProperty.strengthen_p` : the `(p,q)`-property implies the `(p',q)`-property for `p ≤ p'`.
* `HasPQProperty.weaken_q`     : the `(p,q)`-property implies the `(p,q')`-property for `q' ≤ q`.
* `exists_transversal_of_nonempty` : every family of nonempty sets has a transversal of size `≤ |s|`.
* `exists_transversal_of_pqProperty_full` : the `(|s|, q)`-property yields a transversal of size `≤ |s| - q + 1`.
-/


open Finset

open HadwigerDebrunner

variable {ι X : Type*}



/-
Strengthening `p`: the `(p,q)`-property implies the `(p',q)`-property whenever
`p ≤ p'`.  (Among every `p'` members, look at any `p` of them.)
-/

/-
Weakening `q`: the `(p,q)`-property implies the `(p,q')`-property whenever
`q' ≤ q`.  (A common point of `q` sets is a common point of any `q'` of them.)
-/

/-
A family of nonempty sets always has a transversal of size at most `|s|`:
pick one point from each member.
-/
theorem exists_transversal_of_nonempty (s : Finset ι) (F : ι → Set X)
    (hne : ∀ i ∈ s, (F i).Nonempty) :
    ∃ T : Finset X, IsTransversal T s F ∧ T.card ≤ s.card := by
  by_contra! h;
  convert h ( Finset.image ( fun i : s => Classical.choose ( hne i i.2 ) ) Finset.univ ) ?_;
  any_goals exact Classical.decEq X;
  · simp +decide;
    grind +locals;
  · intro i hi; have := Classical.choose_spec ( hne i hi ) ; aesop;



-- !-- Lab Notes -- !--
/-
## Team loop for `Combinatorial.lean`

### Hypothesis (Hypothesizer)
The Hadwiger–Debrunner `(p,q)` theorem is usually presented as one monolithic
statement entangling combinatorics (the `(p,q)`-property and transversals) with
deep geometry (fractional Helly, LP duality in the Alon–Kleitman proof).  Bold
conjecture: the *combinatorial* layer is entirely independent of dimension and of
the set class (convex vs. splinter), and can be isolated and proved on its own
with elementary tools, leaving the geometry to enter through a single scalar — a
Helly number.

### Experiment (Experimenter)
We formalised the `(p,q)`-property (`HasPQProperty`) and transversals
(`IsTransversal`) over an arbitrary family `F : ι → Set X` indexed by a `Finset`.
We then attempted four claims:
* `HasPQProperty.strengthen_p` — monotone in `p` (look at any `p` of the `p'`).
* `HasPQProperty.weaken_q`     — monotone in `q` (a common point of `q` sets is
  common to any `q'` of them).
* `exists_transversal_of_nonempty` — choice function over `s.attach`.
* `exists_transversal_of_pqProperty_full` — the headline elementary bound
  `τ ≤ |s| - q + 1` obtained by piercing the `q`-wise common members with one
  point and the rest individually (reusing `exists_transversal_of_nonempty` on
  the complement `s \ B`).
All four compile with no `sorry` and only the standard axioms.

### Analysis (Analyst)
Everything in this file is *true and easy* once stated over `Finset`-indexed
families; the truncated natural subtraction in the bound even let us drop the
hypothesis `q ≤ |s|` (it is automatically correct).  The genuinely hard,
dimension-dependent content does **not** live here — it lives in the Helly number,
which is exactly what `HellyBridge.lean` supplies.  The structural pattern: the
`(p,q)` theory factors as `combinatorics × (one Helly number)`.

### Critique (Critic)
None of the four results is vacuous: each is a universally quantified implication
with satisfiable hypotheses (e.g. take all `F i` equal to one fixed nonempty
set).  None is closed by a single `simp`/`decide`: the proofs use `induction`-free
but genuine steps — `Finset.exists_subset_card_eq`, antitone `biInter`, classical
choice over `attach`, and a `card_sdiff`/`omega` cardinality calculation.  The
bound `|s| - q + 1` is *not* the dimension-independent bound `N(d,p,q)` of the
full theorem; it depends on `|s|`.  Closing that gap is the deep open part and is
recorded in `FUTURE_DIRECTIONS.md`.

### Synthesis (PI)
This file is the reusable, set-class agnostic core.  `HellyBridge.lean` plugs in
the Helly number `d+1` (convex, via Mathlib's `Convex.helly_theorem`) and `2d+1`
(splinter, via Arocha–Bracho–Montejano) to obtain genuine geometric corollaries.
-/
open HadwigerDebrunner in
theorem solution{s : Finset ι} {F : ι → Set X} {q : ℕ}
    (hne : ∀ i ∈ s, (F i).Nonempty)
    (hpq : HasPQProperty s F s.card q) :
    ∃ T : Finset X, IsTransversal T s F ∧ T.card ≤ s.card - q + 1 := by
  classical
  obtain ⟨B, hBs, hBcard, hBne⟩ := hpq s (Finset.Subset.refl s) rfl
  obtain ⟨t₀, ht₀⟩ := hBne
  obtain ⟨R, hR, hRcard⟩ := exists_transversal_of_nonempty (s \ B) F
    (fun i hi => hne i (Finset.mem_sdiff.1 hi).1)
  refine ⟨insert t₀ R, ?_, ?_⟩
  · intro i hi
    by_cases hiB : i ∈ B
    · exact ⟨t₀, Finset.mem_insert_self _ _, Set.mem_iInter₂.1 ht₀ i hiB⟩
    · obtain ⟨t, htR, htF⟩ := hR i (Finset.mem_sdiff.2 ⟨hi, hiB⟩)
      exact ⟨t, Finset.mem_insert_of_mem htR, htF⟩
  · have hcard : (s \ B).card = s.card - q := by
      rw [Finset.card_sdiff_of_subset hBs, hBcard]
    calc (insert t₀ R).card ≤ R.card + 1 := Finset.card_insert_le _ _
      _ ≤ (s \ B).card + 1 := by omega
      _ = s.card - q + 1 := by rw [hcard]
