-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eventually_uniform_fixedPrimorialFiniteFourierCorrection_sieveLevel
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:53:30.102959+00:00
-- url     : https://prove2.me/submissions/e6b6afd4-ad85-48aa-9079-01bbcb0553ef

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierEulerNormalization
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_threshold_cutoffZetaSystemFactor_close
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_normalizedSmallPrimeZetaCorrection_sieveLevel_fixed

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real













theorem maxAPForms_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < maxAPForms k := by
  exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)

theorem sieveExponent_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < sieveExponent k := by
  rw [sieveExponent]
  apply inv_pos.mpr
  exact_mod_cast
    Nat.mul_pos (by norm_num) (maxAPForms_pos hk)





















/-- The sieve level tends to infinity for every progression length in the
nontrivial range. -/
theorem tendsto_sieveLevel_atTop {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (sieveLevel k) atTop atTop := by
  change Tendsto
    (fun N : ℕ ↦ ⌊(N : ℝ) ^ sieveExponent k⌋₊)
    atTop atTop
  simpa [Function.comp_def] using
    tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (sieveExponent_pos hk)).comp
        tendsto_natCast_atTop_atTop)







end Wikipedia.SzemeredisTheorem

end

section




/-!
# Normalized completed Euler model on CFZ carry blocks

This file assembles three pieces that were previously separate:

* the exact Selberg/Fourier/singular-zeta normalization;
* the exact small-prime/large-prime factorization for a carry block;
* the uniform limits of the normalized small-prime correction, completed
  zeta factor, and large-prime correction.

The resulting pointwise identity is the normalized form of the *completed
Euler model*.  It deliberately does not identify that model with the
finite `d ≤ R` divisor sum; the honest truncation-to-Euler splice remains a
separate analytic theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators





/-! ## Uniform convergence of the residual factors -/

/-- The completed finite zeta factor tends to one along any growing
Fourier box, provided the cutoff scale tends to infinity. -/
theorem tendsto_cutoffZetaSystemFactor_on_growing_box
    {κ : Type*} [Fintype κ]
    (R : ℕ → ℕ) (t u : ℕ → κ → ℝ)
    (hR : Tendsto R atTop atTop)
    (ht :
      ∀ᶠ n in atTop, ∀ q,
        |t n q| ≤ Real.sqrt (Real.log (R n)))
    (hu :
      ∀ᶠ n in atTop, ∀ q,
        |u n q| ≤ Real.sqrt (Real.log (R n))) :
    Tendsto
      (fun n => cutoffZetaSystemFactor (R n) (t n) (u n))
      atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R₀, hclose⟩ :=
    exists_threshold_cutoffZetaSystemFactor_close
      (κ := κ) hε
  have hR₀ : ∀ᶠ n in atTop, R₀ ≤ R n :=
    hR (eventually_ge_atTop R₀)
  filter_upwards [hR₀, ht, hu] with n hRn htn hun
  simpa only [dist_eq_norm] using
    hclose (R n) hRn (t n) (u n) htn hun



end Wikipedia.SzemeredisTheorem

end

section




/-!
# Fixed-primorial Fourier schedules

The Green--Tao parameter order first chooses a large primorial cutoff `w`
and then lets the cyclic modulus tend to infinity.  This file records the
analytic consequences of that order for the concrete sieve level
`sieveLevel k N`.

For fixed `w`, the conventional Fourier radius

`T N = sqrt (log (sieveLevel k N))`

is already small enough for the finite small-prime correction.  Indeed its
quadratic error scale is `O_w(1 / log (sieveLevel k N))`.  Thus no smaller
sub-box is needed.

The large-prime correction has a different quantifier order.  For a fixed
cutoff it need not converge to one as the carry block varies.  What the
uniform prime-square estimate gives, and what the Green--Tao argument
actually uses, is:

`∀ ε > 0, ∃ w₀, ∀ carry blocks with w ≥ w₀, ‖largeCorrection - 1‖ < ε`.

The results below record the fixed-`w` limits and this uniform tail
statement side by side, together with a completed-correction wrapper that
isolates the exact remaining large-prime hypothesis.  They deliberately do
not assert a false fixed-`w` limit for the actual carry correction.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## The fixed-primorial phase scale -/









/-! ## Fixed-primorial finite correction limits -/



/-- The completed finite zeta factor also tends to one on the same box. -/
theorem tendsto_cutoffZetaSystemFactor_sieveLevel_sqrt_log
    {κ : Type*} [Fintype κ]
    {k : ℕ} (hk : 3 ≤ k)
    (t u : ℕ → κ → ℝ)
    (ht :
      ∀ᶠ N in atTop, ∀ q,
        |t N q| ≤
          Real.sqrt (Real.log (sieveLevel k N)))
    (hu :
      ∀ᶠ N in atTop, ∀ q,
        |u N q| ≤
          Real.sqrt (Real.log (sieveLevel k N))) :
    Tendsto
      (fun N =>
        cutoffZetaSystemFactor
          (sieveLevel k N) (t N) (u N))
      atTop (𝓝 1) :=
  tendsto_cutoffZetaSystemFactor_on_growing_box
    (sieveLevel k) t u
    (tendsto_sieveLevel_atTop hk) ht hu

/-- The two residual factors controlled solely by the fixed primorial and
the Fourier box converge jointly to one. -/
theorem tendsto_fixedPrimorialFiniteFourierCorrection_sieveLevel
    {κ : Type*} [Fintype κ]
    {k w : ℕ} (hk : 3 ≤ k) (hw : 2 ≤ w)
    (t u : ℕ → κ → ℝ)
    (ht :
      ∀ᶠ N in atTop, ∀ q,
        |t N q| ≤
          Real.sqrt (Real.log (sieveLevel k N)))
    (hu :
      ∀ᶠ N in atTop, ∀ q,
        |u N q| ≤
          Real.sqrt (Real.log (sieveLevel k N))) :
    Tendsto
      (fun N =>
        normalizedSmallPrimeZetaCorrection
            (sieveLevel k N) w (t N) (u N) *
          cutoffZetaSystemFactor
            (sieveLevel k N) (t N) (u N))
      atTop (𝓝 1) := by
  simpa using
    (tendsto_normalizedSmallPrimeZetaCorrection_sieveLevel_fixed
        hk hw t u ht hu).mul
      (tendsto_cutoffZetaSystemFactor_sieveLevel_sqrt_log
        hk t u ht hu)



/-! ## The honest large-prime tail bridge -/



end Wikipedia.SzemeredisTheorem

end
/-!
# Uniform finite Fourier correction on the Green--Tao box

For a fixed primorial cutoff, the small-prime normalization and the
completed finite zeta factor converge jointly to one along every sequence
of Fourier parameters in the box of radius

`sqrt (log (sieveLevel k N))`.

This file upgrades that sequential statement to uniform convergence on
the whole box.  A failure of uniformity would provide cofinally many bad
indices.  Choosing a bad pair at those indices and zero elsewhere gives a
single box-valued sequence contradicting
`tendsto_fixedPrimorialFiniteFourierCorrection_sieveLevel`.

The final theorem intersects these estimates over the finite type of
selected CFZ exponents.  No large-prime Euler correction occurs here.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology

open Wikipedia.SzemeredisTheorem in
/-- For a fixed finite index type and primorial cutoff, the product of the
two finite Fourier corrections is eventually uniformly close to one on
the full Green--Tao Fourier box. -/
theorem
    solution
    {κ : Type*} [Fintype κ]
    {k w : ℕ} (hk : 3 ≤ k) (hw : 2 ≤ w)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (t u : κ → ℝ),
        (∀ q,
          |t q| ≤
            Real.sqrt (Real.log (sieveLevel k N))) →
        (∀ q,
          |u q| ≤
            Real.sqrt (Real.log (sieveLevel k N))) →
        ‖normalizedSmallPrimeZetaCorrection
              (sieveLevel k N) w t u *
            cutoffZetaSystemFactor
              (sieveLevel k N) t u -
          1‖ < ε := by
  classical
  let radius : ℕ → ℝ :=
    fun N => Real.sqrt (Real.log (sieveLevel k N))
  let Bad :
      (N : ℕ) →
        (κ → ℝ) → (κ → ℝ) → Prop :=
    fun N t u =>
      (∀ q, |t q| ≤ radius N) ∧
        (∀ q, |u q| ≤ radius N) ∧
          ε ≤
            ‖normalizedSmallPrimeZetaCorrection
                  (sieveLevel k N) w t u *
                cutoffZetaSystemFactor
                  (sieveLevel k N) t u -
              1‖
  let witness :
      ℕ → ((κ → ℝ) × (κ → ℝ)) :=
    fun N =>
      if h : ∃ t u, Bad N t u then
        (Classical.choose h,
          Classical.choose (Classical.choose_spec h))
      else
        (0, 0)
  have witness_spec
      (N : ℕ) (hN : ∃ t u, Bad N t u) :
      Bad N (witness N).1 (witness N).2 := by
    simp only [witness, dif_pos hN]
    exact Classical.choose_spec (Classical.choose_spec hN)
  have hwitness :
      ∀ N q, |(witness N).1 q| ≤ radius N := by
    intro N q
    by_cases hN : ∃ t u, Bad N t u
    · exact (witness_spec N hN).1 q
    · simp [witness, hN, radius]
  have hvitness :
      ∀ N q, |(witness N).2 q| ≤ radius N := by
    intro N q
    by_cases hN : ∃ t u, Bad N t u
    · exact (witness_spec N hN).2.1 q
    · simp [witness, hN, radius]
  have hlimit :
      Tendsto
        (fun N =>
          normalizedSmallPrimeZetaCorrection
                (sieveLevel k N) w
                (witness N).1 (witness N).2 *
              cutoffZetaSystemFactor
                (sieveLevel k N)
                (witness N).1 (witness N).2)
        atTop (𝓝 1) := by
    apply
      tendsto_fixedPrimorialFiniteFourierCorrection_sieveLevel
        hk hw
    · exact Filter.Eventually.of_forall hwitness
    · exact Filter.Eventually.of_forall hvitness
  have hclose :
      ∀ᶠ N : ℕ in atTop,
        ‖normalizedSmallPrimeZetaCorrection
              (sieveLevel k N) w
              (witness N).1 (witness N).2 *
            cutoffZetaSystemFactor
              (sieveLevel k N)
              (witness N).1 (witness N).2 -
          1‖ < ε := by
    have hdist :=
      (Metric.tendsto_nhds.mp hlimit) ε hε
    simpa only [dist_eq_norm] using hdist
  rw [eventually_atTop] at hclose ⊢
  obtain ⟨N₀, hN₀⟩ := hclose
  refine ⟨N₀, fun N hN t u ht hu => ?_⟩
  by_contra hfar
  have hbad : Bad N t u := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [radius] using ht
    · simpa only [radius] using hu
    · simpa only [not_lt] using hfar
  have hchosen := witness_spec N ⟨t, u, hbad⟩
  exact
    (not_lt_of_ge hchosen.2.2)
      (hN₀ N hN)
