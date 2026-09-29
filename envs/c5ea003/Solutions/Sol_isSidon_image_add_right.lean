-- Prove2me | solution 1 for isSidon_image_add_right
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:16:53.471148+00:00
-- url     : https://prove2.me/submissions/41d0c1aa-e3d9-4332-a0e4-f6d346a28453

-- Sol generated from Shared/SidonSetsSymmetry.lean
import Mathlib
import Definitions.Def_Shared_SidonSetsCyclic
import Definitions.Def_Shared_SidonSetsErdosTuran
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




theorem solution(A : Finset M) (t : M) :
    IsSidon (A.image (· + t)) ↔ IsSidon A := by
  constructor
  · intro h a ha b hb c hc d hd hsum
    have hmem : ∀ {x : M}, x ∈ A → x + t ∈ A.image (· + t) := fun hx =>
      Finset.mem_image.mpr ⟨_, hx, rfl⟩
    have hsum' : (a + t) + (b + t) = (c + t) + (d + t) := by
      rw [show (a + t) + (b + t) = (a + b) + (t + t) by abel,
        show (c + t) + (d + t) = (c + d) + (t + t) by abel, hsum]
    rcases h _ (hmem ha) _ (hmem hb) _ (hmem hc) _ (hmem hd) hsum' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨add_right_cancel h1, add_right_cancel h2⟩
    · exact Or.inr ⟨add_right_cancel h1, add_right_cancel h2⟩
  · intro h a ha b hb c hc d hd hsum
    simp only [Finset.mem_image] at ha hb hc hd
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨d', hd', rfl⟩ := hd
    have hsum' : a' + b' = c' + d' := by
      have : (a' + b') + (t + t) = (c' + d') + (t + t) := by
        rw [show (a' + b') + (t + t) = (a' + t) + (b' + t) by abel,
          show (c' + d') + (t + t) = (c' + t) + (d' + t) by abel]
        exact hsum
      exact add_right_cancel this
    rcases h a' ha' b' hb' c' hc' d' hd' hsum' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
    · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
