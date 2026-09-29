-- Prove2me | solution 1 for SLEInterface.transport_frequently_event
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:21.271223+00:00
-- url     : https://prove2.me/submissions/376a654d-e619-41b1-8ea2-03fc5980679c

-- Sol generated from Probability/ConformalInvariance.lean
import Mathlib
import Definitions.Def_Probability_BrocardBorelCantelli
import Definitions.Def_Probability_ConformalInvariance
/-
# A measurable interface for conformal covariance of random curves

The analytic construction of Schramm–Loewner evolution is separated here from
its functorial content.  A simply connected domain equipped with a conformal
chart has a measurable curve space, while a reference law lives on a standard
curve space.  Pulling that law back through a chart produces the domain law.
The principal result proves that this construction is independent of the chart
whenever transition maps preserve the reference law.

This formulation isolates three structural consequences used throughout the
probability theory of random interfaces: coherence under composition, recovery
under inverse transport, and invariance of all measurable curve events.  The
last section links conformal transport with a Borel–Cantelli estimate from the
probability catalog: summable exceptional events remain almost surely finite
after a measurable equivalence of curve spaces.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): A chart-based construction of an interface law should
  descend to an intrinsic domain law exactly when every chart transition
  preserves the standard law. Six falsifiable conjectures were ranked by impact:
  full chart descent; covariance under non-bijective conformal maps;
  reconstruction from finite-dimensional driving observables; compatibility
  with time reversal; stability under Carathéodory domain limits; and functorial
  coupling of several interfaces.
Experiment (Experimenter): Transport was tested first on finite curve spaces,
  where charts are permutations.  Composition and inverse transport survived;
  the non-bijective version failed because inverse transport cannot recover mass
  merged by the map.  The surviving statement was then formulated for arbitrary
  measurable equivalences.
Analysis (Analyst): Bijectivity, rather than complex differentiability, is the
  decisive ingredient in chart independence.  The specifically analytic SLE
  burden is therefore concentrated in proving that transition maps preserve the
  standard law.  Once this is known, event probabilities and null exceptional
  sets descend formally.
Critique (Critic): No existence claim for the Loewner chain or Brownian driving
  process is hidden in the interface.  The chart-transition hypothesis is
  explicit and indispensable.  Measurability is retained on both sides, and the
  inverse theorem rules out a vacuous one-way covariance statement.
Synthesis (Principal Investigator): The resulting descent theorem gives a clean
  boundary between conformal analysis and probability.  A transported
  Borel–Cantelli theorem shows that almost-sure finiteness statements are also
  intrinsic under changes of chart.
-- !-- Lab Notes -- !--
-/

open Filter MeasureTheory

open SLEInterface











open SLEInterface in
theorem solution{X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (E : ℕ → Set X)
    (hE : ∀ n, MeasurableSet (E n)) :
    transport e μ {y | ∃ᶠ n in atTop, y ∈ e '' E n} =
      μ {x | ∃ᶠ n in atTop, x ∈ E n} := by
  have hfreq : {y | ∃ᶠ n in atTop, y ∈ e '' E n} =
      e '' {x | ∃ᶠ n in atTop, x ∈ E n} := by
    ext y
    constructor
    · intro hy
      have hevent : ∀ᶠ n in atTop, (y ∈ e '' E n ↔ e.symm y ∈ E n) := by
        filter_upwards [] with n
        constructor
        · rintro ⟨x, hx, hxy⟩
          subst y
          simpa using hx
        · intro hx
          exact ⟨e.symm y, hx, by simp⟩
      have hy' : ∃ᶠ n in atTop, e.symm y ∈ E n :=
        (frequently_congr hevent).mp hy
      exact ⟨e.symm y, hy', by simp⟩
    · rintro ⟨x, hx, rfl⟩
      have hevent : ∀ᶠ n in atTop, (x ∈ E n ↔ e x ∈ e '' E n) := by
        filter_upwards [] with n
        constructor
        · intro hn
          exact ⟨x, hn, rfl⟩
        · rintro ⟨z, hz, hzx⟩
          have : z = x := e.injective hzx
          simpa [this] using hz
      exact (frequently_congr hevent).mp hx
  rw [hfreq, transport, Measure.map_apply e.measurable]
  · rw [e.preimage_image]
  · apply e.measurableSet_image.mpr
    have heq : {x | ∃ᶠ n in atTop, x ∈ E n} = limsup E atTop := by
      ext x
      exact mem_limsup_iff_frequently_mem.symm
    rw [heq]
    exact MeasurableSet.measurableSet_limsup hE
