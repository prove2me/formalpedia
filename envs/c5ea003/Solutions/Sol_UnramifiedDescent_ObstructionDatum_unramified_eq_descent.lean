-- Prove2me | solution 1 for UnramifiedDescent.ObstructionDatum.unramified_eq_descent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:14:26.16513+00:00
-- url     : https://prove2.me/submissions/60d310b1-7028-4852-b039-99d776a9bf33

-- Sol generated from Novelty/UnramifiedDescentObstruction.lean
import Mathlib
import Definitions.Def_Novelty_UnramifiedDescentObstruction

/-!
# Unramified obstruction = descent obstruction: the abstract pairing skeleton

This file isolates and proves, in full generality, the **purely structural core**
of the conjecture

> Let `K` be the function field of a smooth projective geometrically integral curve
> over a `p`-adic field, and `X` a smooth, proper, geometrically integral,
> rationally connected `K`-variety.  Then the unramified cohomological obstruction
> attached to `H³_nr(X, ℚ/ℤ(2))` coincides with the descent obstruction:
> `X(A_K)^{H³_nr} = X(A_K)^{descent}`.

Every obstruction of Brauer–Manin type (and its refinements: descent, étale–Brauer,
unramified) is cut out from the adelic space by **annihilation under a pairing** with
a group of cohomology classes.  Concretely, for a set `T` of adelic points (here an
abstract type `S`) and an abelian group `B` of cohomology classes, one has a
biadditive pairing `S × B → C` (over number fields `C = ℚ/ℤ`, by class-field-theory
reciprocity; over a `p`-adic function field the same formalism applies with the role
of `Br = H²_nr` played by `H³_nr(–, ℚ/ℤ(2))` because the relevant cohomological
dimension is `3 = cd(p-adic field) + 1`).  The obstruction set associated to a family
`H ⊆ B` is the *left orthogonal* `H^⊥ ⊆ S`.

The mathematical heart of any "obstruction A equals obstruction B" theorem is then
the following soft fact, which we make precise and prove here:

* the maps `H ↦ H^⊥` and `T ↦ T^⊥` form an **antitone Galois connection** between
  subsets of `B` and subsets of `S` (`galois`);
* consequently `H ↦ clB H := (H^⊥)^⊥` is a closure operator (`subset_clB`,
  `orthB_clB`), and the obstruction depends **only on the generated subgroup**
  (`orthB_closure`);
* two families of classes cut out the **same** obstruction set iff they have the same
  closure (`obstruction_eq_iff_clB_eq`);
* hence if `Hdesc ⊆ Hunr ⊆ clB Hdesc` — the descent classes are unramified, and the
  unramified classes add nothing to the closure of the descent classes — then the two
  obstruction sets are equal (`obstruction_eq_of_between`).

The last statement is precisely the shape of the target conjecture: the
cohomological-dimension constraint and rational connectedness enter exactly as the
hypothesis `Hunr ⊆ clB Hdesc`, after which the equality of the *sets of adelic points*
is forced by the Galois-connection formalism alone.  We package the whole arithmetic
input into a `ObstructionDatum` and read off `unramified_eq_descent` as a corollary.

A concrete, non-vacuous instance (descent classes properly contained in the
unramified classes, yet equal obstruction sets) lives in
`Catalog.Novelty.UnramifiedDescentModel`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer):  The equality `X(A_K)^{H³_nr} = X(A_K)^{descent}` should
  not depend on the analytic fine structure of adeles at all: every such "obstruction"
  is a left-orthogonal under a pairing, and equality of orthogonals is governed by a
  Galois connection.  Bold form: *all* the classical obstruction comparisons
  (Brauer–Manin vs descent vs étale–Brauer, Stoll's `Sto07`, Skorobogatov's `Sko09`,
  Harari–Skorobogatov–Stoll `HSS15`) are instances of one closure-operator identity.

Experiment (Experimenter):  Formalize `S` (adelic points), `B` (cohomology),
  `P : S → B →+ C` (the reciprocity pairing, additive in the class variable), and the
  two orthogonals.  Prove the Galois connection `galois`, derive the closure operator,
  and prove the subgroup-invariance `orthB_closure` by the kernel argument
  `AddSubgroup.closure_le ((P s).ker)`.  The comparison theorem then drops out as
  `obstruction_eq_of_between`.

Analysis (Analyst):  What survives is *exactly* the soft part: the equality of two
  obstruction loci reduces to the equality of two closed subgroups of cohomology
  (`obstruction_eq_iff_clB_eq`).  What does NOT survive into Lean (true but hard,
  needing the arithmetic geometry of `CT03`/`Har02` and étale cohomology absent from
  Mathlib) is the verification that, over a `p`-adic function field and for a
  rationally connected `X`, the unramified classes really do lie in `clB Hdesc`; that
  is the genuine geometric content and is isolated as the hypothesis
  `unramified_le_closure`.  The split is clean: geometry feeds one inclusion of
  subgroups, formalism does the rest.

Critique (Critic):  Is `obstruction_eq_of_between` vacuous?  No — the companion model
  exhibits `Hdesc ⊊ Hunr` with equal obstruction sets that are proper nonempty subsets
  of `S`, so the hypotheses are simultaneously satisfiable and the conclusion is not
  automatic.  Is anything proved by `rfl`/`decide` alone?  No — the core lemmas use the
  Galois connection and a subgroup-closure / kernel argument.  Hidden corner: the
  pairing must be additive in `B`; we enforce this by typing it as `B →+ C`, faithful
  to the bilinearity of the reciprocity pairing.

Synthesis (PI):  The conjecture's *form* is a theorem: obstruction equality is a
  closure-operator identity, with all arithmetic geometry concentrated in a single
  inclusion of cohomology subgroups.  This mirrors the catalog's GL(1) duality strand
  (`Catalog/Novelty/GaloisDuality.lean`), where a counting coincidence was upgraded to
  a structural isomorphism; here a conjectural set equality is upgraded to a Galois
  closure identity.
-/

open UnramifiedDescent

variable {S B C : Type*} [AddCommGroup B] [AddCommGroup C]







theorem subset_clB (P : S → B →+ C) (H : Set B) : H ⊆ clB P H :=
  fun _b hb _s hs => hs _b hb

/-- The obstruction set is unchanged by passing to the closure: closing up the
classes adds no new constraints on the adelic points. -/
theorem orthB_clB (P : S → B →+ C) (H : Set B) : orthB P (clB P H) = orthB P H := by
  apply Set.Subset.antisymm
  · exact orthB_antitone P (subset_clB P H)
  · intro s hs b hb; exact hb s hs




/-- **Main abstract comparison theorem.**  If the descent classes are unramified
(`Hdesc ⊆ Hunr`) and the unramified classes lie in the obstruction-closure of the
descent classes (`Hunr ⊆ clB Hdesc` — the cohomological-dimension/rational-connectedness
input), then the unramified obstruction set and the descent obstruction set are
**equal**. -/
theorem obstruction_eq_of_between (P : S → B →+ C) {Hdesc Hunr : Set B}
    (h1 : Hdesc ⊆ Hunr) (h2 : Hunr ⊆ clB P Hdesc) :
    orthB P Hunr = orthB P Hdesc := by
  apply Set.Subset.antisymm
  · exact orthB_antitone P h1
  · calc orthB P Hdesc = orthB P (clB P Hdesc) := (orthB_clB P Hdesc).symm
      _ ⊆ orthB P Hunr := orthB_antitone P h2


open ObstructionDatum







open UnramifiedDescent in
theorem solution(D : ObstructionDatum S B C) :
    D.unramifiedObstruction = D.descentObstruction :=
  obstruction_eq_of_between D.pairing D.descent_le_unramified D.unramified_le_closure
