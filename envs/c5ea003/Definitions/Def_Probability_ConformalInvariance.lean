-- Prove2me | Definitions.Def_Probability_ConformalInvariance
-- name    : Probability_ConformalInvariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:19.442454+00:00
-- url     : https://prove2.me/theorems/7d373fb2-b86c-4e6f-92cf-68c63a544f64
-- title:
--   Aether Catalog definitions — Probability_ConformalInvariance
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ConformalInvariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ConformalInvariance.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_BrocardBorelCantelli
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

namespace SLEInterface

/-- Transport a random-interface law along a measurable map of curve spaces. -/
noncomputable def transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (μ : Measure X) : Measure Y := Measure.map f μ

/-- The law on a domain curve space induced from a standard law and a chart to
that standard curve space. -/
noncomputable def chartLaw {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
    (chart : X ≃ᵐ H) (standardLaw : Measure H) : Measure X :=
  transport chart.symm standardLaw








end SLEInterface


