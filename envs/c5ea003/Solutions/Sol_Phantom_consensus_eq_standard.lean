-- Prove2me | solution 1 for Phantom.consensus_eq_standard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:17:50.280017+00:00
-- url     : https://prove2.me/submissions/db7d8ea2-fa7a-4642-9d69-7b3b90ff9f8e

-- Sol generated from Novelty/PhantomTopology.lean
import Mathlib
import Definitions.Def_Novelty_PhantomTopology
/-
# Phantom Topologies: Spaces That Change When You Look at Them

A *phantom topology* on a set `X` is a family of topologies indexed by a set of
"observers" `ι`, i.e. a function `T : ι → TopologicalSpace X`.  Each observer `i`
resolves `X` through their own topology `T i`.  The *real* (consensus) topology is
what **all** observers agree is open:

  `U` is consensus-open  ⇔  `U` is open in every `T i`.

In Mathlib's lattice of topologies (where `t ≤ s` means `t` is *finer* than `s`),
this consensus is exactly the supremum `⨆ i, T i`, whose open sets are precisely
the sets open in every `T i` (`isOpen_iSup_iff`).  Each individual observer is
finer than the consensus (`T i ≤ consensus T`): looking through a single lens can
only *add* resolution; agreement can only *remove* it.

The headline result (`consensus_eq_standard`) is the "two–observer theorem" for
the real line: the ordinary Euclidean topology on `ℝ` is the consensus of exactly
two phantom observers — the **lower-limit** (Sorgenfrey) observer, whose basic
opens are right half-open intervals `[x, b)`, and the **upper-limit** observer,
whose basic opens are left half-open intervals `(a, x]`.  Neither observer alone
sees the Euclidean topology (`lowerTop_ne_standard`, `upperTop_ne_standard`), and
the two observers genuinely disagree (`lowerTop_ne_upperTop`), so the phantom
number of `ℝ` in this representation is exactly two.

-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer):
  H1. The Euclidean topology on `ℝ` is the "intersection" (consensus/supremum in
      the topology lattice) of the lower-limit and upper-limit topologies.
      Rationale: `[x,b)` pins a point from the right, `(a,x]` from the left; a set
      open to both observers is squeezed into a genuine two-sided neighbourhood.
  H2. A single observer over-resolves: the lower-limit observer sees `[0,1)` as
      open, which is not Euclidean-open. Hence one observer is never enough.
  H3 (surprising). The consensus operation is *monotone the "wrong" way*: each
      observer is finer than the consensus, i.e. adding observers can only coarsen
      the agreed topology, never refine it.

Experiment (Experimenter):
  - Modelled `lowerOpen`/`upperOpen` as concrete neighbourhood predicates and
    verified the three `TopologicalSpace` axioms by hand (min/max of interval
    endpoints for finite intersections).
  - Checked the squeeze `(a,x] ∪ [x,b) = (a,b)` numerically before formalising.
  - Confirmed `Ico 0 1` is lower-open but not Euclidean-open (a left ε-ball at 0
    escapes the set).

Analysis (Analyst):
  - H1 survives as `consensus_eq_standard`, the core theorem, with a clean
    two-sided ε argument. The Bool-indexed packaging `consensus_pair_eq_standard`
    shows this is literally a *two*-observer consensus.
  - H2 survives as the `ne_standard` lemmas; the witnesses `[0,1)` / `(0,1]` are
    the sharp obstructions.
  - H3 survives as `observer_le_consensus` (= `le_iSup`), which is exactly the
    counter-intuitive monotonicity: more observers ⇒ coarser reality.

Critique (Critic):
  - `consensus_eq_standard` is not definitional: it equates a hand-rolled sup of
    two custom topologies with Mathlib's metric topology on `ℝ`, proved by a real
    ε–δ neighbourhood argument (`Metric.isOpen_iff`, `abs_lt`, `linarith`).
  - The lower-bound lemmas use genuine witnesses and rule out the trivial
    "one observer suffices" reading, so the phantom number is pinned to 2, not ≤2.
  - No `native_decide`, no `True`, no wrapper types.

Synthesis (PI):
  Reality-as-consensus is a faithful lattice-theoretic notion: the Euclidean line
  is the exact agreement of a left-looking and a right-looking observer, and the
  agreement functor is order-reversing in resolution. This gives a rigorous
  toy-model of "measurement coarsens structure".
-/

open Set

open Phantom

/-! ## The phantom-topology framework -/

variable {X : Type*} {ι : Type*}





/-! ## The two observers on `ℝ` -/





/-! ## Main theorem: `ℝ` is a two-observer consensus -/




/-! ## One observer is not enough -/









open Phantom in
theorem solution:
    lowerTop ⊔ upperTop = (inferInstance : TopologicalSpace ℝ) := by
  apply TopologicalSpace.ext
  ext U
  constructor
  · -- both observers agree ⇒ Euclidean open (two-sided squeeze)
    rintro ⟨hlo, hup⟩
    rw [Metric.isOpen_iff]
    intro x hx
    obtain ⟨b, hb, hbsub⟩ := hlo x hx
    obtain ⟨a, ha, hasub⟩ := hup x hx
    refine ⟨min (x - a) (b - x), by simp only [lt_min_iff]; constructor <;> linarith, ?_⟩
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have h1 : |y - x| < x - a := lt_of_lt_of_le hy (min_le_left _ _)
    have h2 : |y - x| < b - x := lt_of_lt_of_le hy (min_le_right _ _)
    rw [abs_lt] at h1 h2
    rcases le_or_gt x y with hxy | hxy
    · exact hbsub ⟨hxy, by linarith [h2.2]⟩
    · exact hasub ⟨by linarith [h1.1], le_of_lt hxy⟩
  · -- Euclidean open ⇒ open for each observer (each is finer)
    intro hU
    rw [Metric.isOpen_iff] at hU
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨ε, hε, hsub⟩ := hU x hx
      refine ⟨x + ε, by linarith, ?_⟩
      intro y hy
      apply hsub
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> [linarith [hy.1]; linarith [hy.2]]
    · intro x hx
      obtain ⟨ε, hε, hsub⟩ := hU x hx
      refine ⟨x - ε, by linarith, ?_⟩
      intro y hy
      apply hsub
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> [linarith [hy.1]; linarith [hy.2]]
