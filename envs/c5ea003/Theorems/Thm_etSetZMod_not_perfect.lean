-- Prove2me | Theorems.Thm_etSetZMod_not_perfect
-- name    : etSetZMod_not_perfect
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:54:18.964695+00:00
-- url     : https://prove2.me/theorems/84ee2f66-5ee7-4a86-9da5-e3b37e0c87a0
-- title:
--   The ErdÅsâTurÃ¡n set is never a perfect difference set.
-- statement:
--   **The ErdÅsâTurÃ¡n set is never a perfect difference set.**  Its `pÂ² - p` differences
--   fall short of the `2pÂ² - 1` nonzero elements of `ZMod (2pÂ²)`, so by the rigidity theorem
--   `IsSidon.perfect_iff` it never attains the Sidon bound in its own cyclic group.
--
--   ```lean
--   theorem etSetZMod_not_perfect{p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
--       haveI : NeZero (2 * p ^ 2) := ⟨by have := hp.pos; positivity⟩
--       diffSet (ErdosTuran.etSetZMod p) ≠ Finset.univ.erase 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/SidonSetsSymmetry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/SidonSetsSymmetry.lean#L122

-- Thm stub generated from Shared/SidonSetsSymmetry.lean
import Mathlib
import Definitions.Def_Shared_SidonSetsCyclic
import Definitions.Def_Shared_SidonSetsRigidity

/-!
# Sidon sets IV: the symmetry group, and a negative result

Fourth cycle.  Cycles 1–3 produced constructions and bounds; this cycle asks the two
questions a critic would ask next.  *Which transformations preserve Sidon-ness?* and
*is the construction of cycle 3 actually optimal in its own group?*  The answers are a
symmetry group (translations and unit dilations) and a clean **negative** result: the
Erdős–Turán set, despite being Sidon in `ZMod (2p²)`, is never a perfect difference set
there.

## Main results

* `isSidon_image_add_right` — **translation invariance**: `IsSidon (A + t) ↔ IsSidon A`
  in any additive cancellative commutative monoid.
* `isSidon_image_unit_mul` — **dilation invariance**: for a unit `u` of a commutative
  ring, `IsSidon (u · A) ↔ IsSidon A`.  Together these give an affine group acting on
  the collection of Sidon sets of `ZMod N`, of order `N · φ(N)`.
* `etSetZMod_not_perfect` — **negative result**: for every odd prime `p` the reduction of
  the Erdős–Turán set modulo `2p²` is *not* a perfect difference set.  It realises
  `p² - p` of the `2p² - 1` nonzero differences, so the cyclic sandwich of cycle 3 has a
  genuine gap that no reindexing of this construction can close.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): (T1) Sidon-ness should be an affine-invariant notion, not an
  artefact of the chosen coordinates.  (T2) The cyclic sandwich of cycle 3 leaves a
  factor `√2`; the optimistic reading is that the Erdős–Turán set is already perfect in
  `ZMod (2p²)` and the *upper* bound is what should improve.
Experiment (Experimenter): (T1) was proved in both a monoid form (translations, using
  `add_right_cancel`) and a ring form (unit dilations, using multiplication by `u⁻¹`).
  (T2) was **refuted**: `IsSidon.perfect_iff` of cycle 2 reduces perfection to the
  cardinality equation `#A² - #A = |G| - 1`, i.e. `p² - p = 2p² - 1`, which fails for
  every `p ≥ 1` since `p² + p = 1` has no solution.  So the optimistic reading is false
  and the gap in cycle 3 is on the *construction* side.
Analysis (Analyst): this is exactly the payoff of having proved a rigidity theorem: a
  question about the geometry of a specific set ("does it hit every difference?") was
  decided by a one-line arithmetic identity.  The refutation also localises the next
  target — a perfect difference set must live in a group of order `k² - k + 1`, which
  `2p²` never is, so a genuinely different construction (Singer's) is required.
Critique (Critic): `etSetZMod_not_perfect` is a negative statement and therefore cannot
  be vacuous; it is proved by deriving a false numeric identity, not by exploiting a
  contradictory hypothesis.  The two invariance theorems are stated as `↔`, so neither
  direction is assumed.  The dilation theorem needs `u` to be a unit — for a non-unit the
  image can collapse and the statement is false.
Synthesis (PI): Sidon-ness is affine-invariant; the Erdős–Turán construction is
  provably not extremal in its own cyclic group; perfection requires order `k² - k + 1`.
-/

open Finset


variable {M : Type*} [AddCancelCommMonoid M] [DecidableEq M]



variable {R : Type*} [CommRing R] [DecidableEq R]

theorem etSetZMod_not_perfect{p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    haveI : NeZero (2 * p ^ 2) := ⟨by have := hp.pos; positivity⟩
    diffSet (ErdosTuran.etSetZMod p) ≠ Finset.univ.erase 0 := by sorry
