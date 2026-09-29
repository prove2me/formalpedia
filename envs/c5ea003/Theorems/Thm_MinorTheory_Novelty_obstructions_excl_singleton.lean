-- Prove2me | Theorems.Thm_MinorTheory_Novelty_obstructions_excl_singleton
-- name    : MinorTheory.Novelty.obstructions_excl_singleton
-- status  : Disproved
-- author  : @raver1975
-- created : 2026-09-13T04:43:29.14045+00:00
-- url     : https://prove2.me/theorems/b4e84dac-8cdd-425e-9f8a-1fb9c96ab8d8
-- title:
--   The obstruction set of `excl {H}` is exactly `{H}`.
-- statement:
--   The obstruction set of `excl {H}` is exactly `{H}`.
--
--   ```lean
--   theorem MinorTheory.Novelty.obstructions_excl_singleton(H : α) :
--       obstructions (excl ({H} : Set α)) = {H} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/SingleForbiddenMinorLattice.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/SingleForbiddenMinorLattice.lean#L175

-- Thm stub generated from Speculative/AutoResearch/SingleForbiddenMinorLattice.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SingleForbiddenMinorLattice
/-
  The Lattice of Minor-Closed Classes: Ideals, Coavoidance, and Single
  Forbidden Minors
  ====================================================================

  This file extends the order-theoretic backbone of the catalog's theory of
  *minor-closed graph classes* (`Catalog/Probability/OrderFramework.lean`,
open `MinorTheory`),
  single-forbidden-minor characterisation

      `SingleExcludedMinor C ↔ obstructions C is a singleton`

  (over a well-founded partial order modelling the graph-minor relation).  We push
  the *lattice* picture further, locating single-forbidden-minor classes inside the
  complete lattice of minor-closed classes, and we organise the two canonical
  "extremal" constructions that bracket the mission target:

  * `minorIdeal G`   — the principal down-set `↓G = {x | x ≤ G}`, the **smallest**
                       minor-closed class containing `G`.
  * `excl {H}`       — proved here to be the **largest** minor-closed class
                       *avoiding* `H` (i.e. not having `H` as a member), realised
                       concretely as `⋃₀ {C | MinorClosed C ∧ H ∉ C}`.

  Main new results (all 0-sorry):

  * `minorClosed_minorIdeal`            : principal down-sets are minor-closed.
  * `minorIdeal_subset_of_mem`          : `↓G` is the smallest minor-closed class
                                          containing `G`.
  * `excl_singleton_maximal_avoiding`   : any minor-closed class avoiding `H` is
                                          contained in `excl {H}`.
  * `excl_singleton_eq_sUnion_avoiding` : `excl {H}` *is* the union of all
                                          minor-closed classes avoiding `H` — the
                                          unique ⊆-maximal such class.
  * `minorClosed_sandwich`              : every minor-closed `C` containing `G` and
                                          avoiding `H` is sandwiched
                                          `↓G ⊆ C ⊆ excl {H}`.
  * `obstructions_antichain`            : the minimal obstructions of any class form
                                          an antichain (the easy half of
                                          Robertson–Seymour, in lattice form).
  * `singleExcludedMinor_iff_obstructions_singleton`
                                        : capstone, single forbidden minor ⇔ unique
                                          minimal obstruction (well-founded order).

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): the catalog's iff is the "local" statement; the
    mission's "⊆-minimal class has a single forbidden minor" is fundamentally a
    *lattice* statement.  Conjecture: single-forbidden-minor classes are exactly
    the ⊆-maximal classes that avoid a fixed graph, while the dual extremal object
    — the smallest class containing a fixed graph — is a principal ideal that in
    general needs *many* forbidden minors.
  Experiment (Experimenter): formalised `minorIdeal`, `avoiding`, and proved both
    extremal characterisations.  The largest-avoiding identity reduces to two facts
    that need only transitivity of the minor order: `excl {H}` itself avoids `H`,
    and any minor-closed `C` with `H ∉ C` lies inside `excl {H}` because `H ≤ x`
    with `x ∈ C` would force `H ∈ C` by downward closure.
  Analysis (Analyst): the asymmetry is the key insight.  `excl {H}` (one forbidden
    minor) is *maximal* avoiding; `minorIdeal G` (the minimal class containing `G`)
    is generally *not* a single-forbidden-minor class, since its obstruction set is
    the antichain of minimal graphs that are not minors of `G`, which is typically
    large.  So "few forbidden minors" is a feature of *large* (maximal) classes,
    explaining why the mission restricts to ⊆-minimal classes *above a density
    threshold*: the density floor forces the class to be large enough that its
    obstruction antichain collapses to a single graph.
  Critique (Critic): `excl_singleton_maximal_avoiding` needs only a `Preorder`;
    antisymmetry is genuinely required for the obstruction *antichain* and the
    *uniqueness* statements, and well-foundedness for the round trip
    `C = excl (obstructions C)`.  Hypotheses are tracked at minimal strength per
    `H` (`H_not_mem_excl_singleton`), so the avoiding family is non-degenerate.
  Synthesis (PI): the lattice of minor-closed classes has, for each `H`, a unique
    maximal element avoiding `H` (namely `excl {H}`), and the single-forbidden-minor
    classes are precisely these maximal coavoiders.  The density-`3/2` mission
    target is the assertion that ⊆-minimality above the threshold lands you exactly
    on one of these maximal coavoiders.
  -- !-- Lab Notes -- !--
-/

open MinorTheory.Novelty

variable {α : Type*}

/-! ### Preorder layer: minor-closure, exclusion, ideals -/

variable [Preorder α]










/-! ### Coavoidance: `excl {H}` is the largest class avoiding `H` -/







/-! ### Partial-order layer: the obstruction antichain -/

variable [PartialOrder α]

theorem MinorTheory.Novelty.obstructions_excl_singleton(H : α) :
    obstructions (excl ({H} : Set α)) = {H} := by sorry
