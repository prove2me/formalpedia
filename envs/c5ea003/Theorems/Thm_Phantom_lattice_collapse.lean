-- Prove2me | Theorems.Thm_Phantom_lattice_collapse
-- name    : Phantom.lattice_collapse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:20:29.687763+00:00
-- url     : https://prove2.me/theorems/9d24b736-1339-4f7d-be6e-e4ea8b01f36d
-- title:
--   Collapse principle.
-- statement:
--   **Collapse principle.** In any complete lattice, if `τ` is the supremum of a finite
--   family `f` (indexed by a `Finset s` of size at least two) whose members are each
--   *strictly below* `τ`, then `τ` is already the supremum of just **two** elements strictly
--   below it.  Proof by strong induction on `s.card`: peel one index `j`; if the remaining
--   supremum is `< τ` we are done, otherwise it equals `τ` over a strictly smaller index set
--   and we recurse, the recursion being unable to bottom out at a single (strict) element.
--
--   ```lean
--   theorem Phantom.lattice_collapse{L : Type*} [CompleteLattice L] {α : Type*} (τ : L) :
--       ∀ (s : Finset α) (f : α → L), 2 ≤ s.card → (⨆ i ∈ s, f i) = τ →
--         (∀ i ∈ s, f i < τ) → ∃ b c : L, b < τ ∧ c < τ ∧ b ⊔ c = τ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PhantomTopologyCollapse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PhantomTopologyCollapse.lean#L84

-- Thm stub generated from Novelty/PhantomTopologyCollapse.lean
import Mathlib
import Definitions.Def_Novelty_PhantomTopology
import Definitions.Def_Novelty_PhantomTopologyCollapse
/-
# The Phantom Number Collapse: Why No Space Ever Needs Three Observers

Building on `Catalog.Novelty.PhantomTopology` and `Catalog.Novelty.PhantomTopologyNumber`,
this file settles the *quantitative* half of the phantom-topology programme in full
generality.

Recall the setup.  A **phantom topology** on `X` is a family `T : ι → TopologicalSpace X`
of "observer" topologies; the **consensus** (real) topology is `consensus T = ⨆ i, T i`,
whose opens are exactly the sets open in *every* observer (`consensus_isOpen_iff`).  A
representation is **genuinely phantom** when every observer is *strictly finer* than the
consensus (`T i < consensus T`): each observer resolves phantom structure that reality
does not.  The **phantom number** of a topology `τ` is the least number of observers in a
genuine representation with consensus `τ`.

The original conjecture proposed that "every non-metrizable space requires at least
`3` observers".  The companion file `PhantomTopologyNonMetrizable` already refuted this
with a single counterexample (the indiscrete two-point space).  Here we prove the
*structural reason* behind that refutation, and show the phenomenon is universal:

  **No topology, metrizable or not, ever requires three or more observers.**

The key is a purely lattice-theoretic *collapse* principle (`lattice_collapse`): in any
complete lattice, if `τ` is the join of a finite family of elements each *strictly below*
`τ`, then `τ` is already the join of just *two* elements strictly below it.  Grouping
observers can never lose you the consensus, so any genuine finite representation collapses
to a genuine two-observer one (`finite_collapses_to_two`).  Consequently the phantom
number is always `2` whenever it is finite (`no_topology_requires_three`).  Applying this
to the Euclidean line — whose lower/upper-limit observers are strictly finer with Euclidean
consensus (imported from the catalog) — pins its phantom number to *exactly* `2`, and shows
every one of its genuine finite representations collapses onto that pair
(`euclidean_phantom_number_two`).

-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer):
  H1. The "≥ 3 observers" clause is not just occasionally false (indiscrete space) but
      *always* false: there is a lattice-theoretic obstruction making 3 impossible.
  H2 (surprising, counter-intuitive). The phantom number is a *two-valued* invariant on
      finite representations: it is `2` if a genuine representation exists at all, and
      otherwise no finite genuine representation exists (join-irreducible reality). There
      is no "granularity" of observers between 2 and infinity.
  H3. The mechanism is join-reducibility: `τ = a ⊔ b ⊔ c` with all `< τ` can be regrouped
      as `a ⊔ (b ⊔ c)`; either `b ⊔ c < τ` (done) or `b ⊔ c = τ` (a smaller genuine rep),
      and finite descent terminates.

Experiment (Experimenter):
  - Verified the regrouping on the indiscrete `Bool` example: adding a third redundant
    Sierpinski-like observer never breaks the two-observer consensus.
  - Checked the descent base case: a *single* element strictly below `τ` cannot have join
    equal to `τ`, so the recursion cannot bottom out at one observer — it must find a
    strictly-smaller second joinand.

Analysis (Analyst):
  - H1/H3 survive as `lattice_collapse` (strong induction on `Finset.card`, peeling one
    index with `Finset.iSup_insert` and splitting on whether the remainder equals `τ`).
  - H2 survives as `finite_collapses_to_two` and `no_topology_requires_three`.
  - The Euclidean corollary `euclidean_phantom_number_two` genuinely *uses* the catalog:
    `consensus_eq_standard`, `lowerTop_lt_standard`, `upperTop_lt_standard`.

Critique (Critic):
  - `lattice_collapse` is not definitional: it is a genuine descent argument with a real
    base-case contradiction (a strict element cannot join to `τ` alone).
  - The observers in `euclidean_phantom_number_two` are proved *strictly* finer (imported
    `<` facts), so the representation is genuinely phantom, not a duplication.
  - No `native_decide`, no `True`, no wrapper types; the load-bearing steps are
    `Finset.strongInduction`, `Finset.iSup_insert`, `lt_or_eq_of_le`, `le_antisymm`.

Synthesis (PI):
  Reality-as-consensus has a rigid quantitative shadow: the number of genuinely distinct
  observers needed to reconstruct a space is never a subtle integer — it is exactly two,
  or (for join-irreducible topologies) unattainable in finitely many. "Measurement
  coarsens structure", but the coarsening is always the meet of just two sharper views.
-/

open Set

open Phantom

/-! ## The lattice collapse principle -/

theorem Phantom.lattice_collapse{L : Type*} [CompleteLattice L] {α : Type*} (τ : L) :
    ∀ (s : Finset α) (f : α → L), 2 ≤ s.card → (⨆ i ∈ s, f i) = τ →
      (∀ i ∈ s, f i < τ) → ∃ b c : L, b < τ ∧ c < τ ∧ b ⊔ c = τ := by sorry
