-- Prove2me | Definitions.Def_Novelty_UniversalMathematics
-- name    : Novelty_UniversalMathematics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:26.958384+00:00
-- url     : https://prove2.me/theorems/2a197900-d637-4fcf-b29a-251daf99ccac
-- title:
--   Aether Catalog definitions — Novelty_UniversalMathematics
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalMathematics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalMathematics.lean by skeleton subtraction
import Mathlib

/-!
# Universal Mathematics: the invariant core shared by every consistent theory

Would a non-human intelligence — alien, artificial, or independently evolved —
discover *the same* mathematics that we do?  The question only becomes precise
once we fix what "the same mathematics" means.  Here we adopt the following
definition.  Fix a background notion of logical consequence, modelled by a
*consequence operator* `C` sending a set of assumptions to the set of statements
it entails.  A *theory* is a set of assumptions; its *theorems* are `C` of those
assumptions.  Given a base theory `base` (think: the axioms of arithmetic),
its **universal mathematics** is the intersection of the theorem-sets of *all*
consistent theories that extend it:

`Universal base = ⋂ { C Δ | base ⊆ Δ and Δ is consistent }`.

Intuitively this is the body of results that *survives* in every consistent way
of extending the base — the part of mathematics no consistent extension can
disown.

The central results of this file are:

* `peano_universal` — every theorem of the base is a theorem of every consistent
  extension.  Reading `base` as the Peano axioms, this is the precise sense in
  which *arithmetic is universal*: whatever richer consistent system a foreign
  intelligence adopts, it necessarily proves everything arithmetic proves.

* `universal_eq_base` — the universal mathematics of a consistent base is
  *exactly* its own theorem-set.  So the shared, extension-invariant core is
  neither larger nor smaller than the base theory: it is the base theory.

* `consistent_downward` — consistency is inherited by sub-theories.

Alongside these we record the structural fact that a consequence operator is a
*closure operator* in the order-theoretic sense (`toClosureOperator`), linking
the logic of provability to the lattice theory of closure systems, and we
exhibit an explicit model (`trivialSystem`) witnessing that the hypotheses are
satisfiable and that consistent extensions can be *strictly* larger than the
base while the universal core stays put.
-/

open Set

/-- A **consequence operator** on a type `S` of statements: `C Γ` is the set of
statements entailed by the assumptions `Γ`.  The three laws are Tarski's axioms
for a consequence relation — inclusion, monotonicity, and idempotence — which
are exactly the axioms of a closure operator on the powerset of `S`. -/
structure ConseqSystem (S : Type*) where
  /-- The consequence (deductive closure) operator. -/
  C : Set S → Set S
  /-- Every assumption is a consequence of itself: `Γ ⊆ C Γ`. -/
  subset_closure : ∀ Γ, Γ ⊆ C Γ
  /-- More assumptions entail more consequences. -/
  mono : ∀ ⦃Γ Δ : Set S⦄, Γ ⊆ Δ → C Γ ⊆ C Δ
  /-- Consequences of consequences are already consequences (cut). -/
  idem : ∀ Γ, C (C Γ) ⊆ C Γ

namespace ConseqSystem

variable {S : Type*} (L : ConseqSystem S)



/-- A theory `Γ` is **consistent** when it does not entail *everything*: some
statement escapes its deductive closure. -/
def IsConsistent (Γ : Set S) : Prop := L.C Γ ≠ Set.univ

/-- The **universal mathematics** of a base theory: the theorems shared by every
consistent theory extending it. -/
def Universal (base : Set S) : Set S :=
  ⋂₀ {T | ∃ Δ, base ⊆ Δ ∧ L.IsConsistent Δ ∧ T = L.C Δ}









end ConseqSystem

/-!
## An explicit model witnessing non-vacuity

The identity consequence operator on the natural numbers (where a statement is a
consequence of `Γ` exactly when it belongs to `Γ`) is a genuine consequence
system.  It shows the axioms are satisfiable, that consistent theories exist,
and — crucially — that a consistent extension can be *strictly* larger than the
base even though the universal (extension-invariant) core does not grow.
-/

/-- The identity ("no deduction") consequence system on `ℕ`: theorems are just
the assumptions.  A minimal but genuine model of the axioms. -/
def trivialSystem : ConseqSystem ℕ where
  C := id
  subset_closure _ := subset_rfl
  mono := fun _ _ h => h
  idem _ := subset_rfl

namespace trivialSystem





end trivialSystem

/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  "Universal mathematics" — the theorems provable
in *any* sufficiently expressive consistent framework — should be a robust,
observer-independent object.  Bold conjecture: the invariant core shared by all
consistent extensions of a base theory is *exactly* the base theory, so that a
base such as arithmetic is "universal" in the strongest possible sense: present,
and only just present, in every consistent extension.

**Experiment (Experimenter).**  We modelled logical consequence abstractly by
Tarski's closure axioms (`ConseqSystem`), avoiding any commitment to a specific
syntax.  Consistency was captured as "does not entail everything"
(`C Γ ≠ univ`), which needs no negation symbol.  Universality (`peano_universal`)
fell straight out of monotonicity.  The equation `Universal = C base` split into
two inclusions: `base_subset_universal` (monotonicity again) and
`universal_subset_base` (the base is a consistent extension of itself, so it is
one of the sets being intersected).

**Analysis (Analyst).**  Two structural patterns unify the results.  (1) A
consequence operator *is* a closure operator; recording this
(`toClosureOperator`) imports the entire order theory of closure systems for
free and explains why closed theories form a complete lattice.  (2) The
universal core is a *fixed point* of closure that is also a lower bound of a
family of theories; the base achieves the bound because reflexivity places it
inside the family.

**Critique (Critic).**  Is `universal_eq_base` vacuous?  No: `trivialSystem`
supplies a concrete model where the base is consistent (`base_consistent`), yet
a *strictly* larger consistent extension exists (`strict_extension`,
`extension_consistent`).  Thus the intersection genuinely ranges over more than
the base, and the theorem asserts a real coincidence rather than a triviality.
Is consistency needed?  Yes: `universal_subset_base` uses it essentially — an
inconsistent base is not among the consistent extensions, and the intersection
can then overshoot.  The downward lemma `consistent_downward` shows the
hypothesis is well behaved under passing to sub-theories.

**Synthesis (Principal Investigator).**  The extension-invariant core of a
consistent theory is the theory itself.  Universality is therefore not a matter
of *how much* a system proves but of *what every consistent enrichment must
retain*.  This reframes the "would aliens discover our mathematics?" question:
the answer is that any consistent framework extending a common base necessarily
contains that base's theorems, and the shared part is precisely the base — no
more (extensions may diverge above it) and no less (nothing in the base can be
dropped).
-/


