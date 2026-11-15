-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_threshold_wTrickedPrimeWeight_le_cyclicMajorant
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:58:28.681022+00:00
-- url     : https://prove2.me/submissions/1776ca5f-9fc3-47e4-80ac-68753b65aea0

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_threshold_wTrickedPrimeWeight_le_sieveMajorant

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



theorem eventually_two_le_sieveLevel {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ sieveLevel k N :=
  (tendsto_sieveLevel_atTop hk).eventually
    (eventually_ge_atTop 2)



end Wikipedia.SzemeredisTheorem

end

section







/-!
# Smooth sieve cutoffs

This file packages the smooth cutoff used by the Goldston--Yıldırım
divisor sum.  It also constructs a concrete cutoff from Mathlib's smooth
bump-function infrastructure and proves that its derivative-square
normalizer is positive.
-/

namespace Wikipedia.SzemeredisTheorem

open Function Set MeasureTheory
open scoped ContDiff



namespace SmoothSieveCutoff













theorem normalizer_nonneg (χ : SmoothSieveCutoff) :
    0 ≤ χ.normalizer := by
  rw [normalizer]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro x _
  exact sq_nonneg _







end SmoothSieveCutoff











end Wikipedia.SzemeredisTheorem

end

section






/-!
# Smooth truncated divisor sums

The Goldston--Yıldırım majorant is the square of a smoothly truncated
Möbius divisor sum.  This file fixes the normalization and proves the exact
prime-value identity used for pointwise domination of the W-tricked prime
weight.  The later linear-forms estimate is deliberately separated from
these elementary identities.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators





















theorem smoothSelbergWeight_nonneg
    (χ : ℝ → ℝ) (R n : ℕ) :
    0 ≤ smoothSelbergWeight χ R n :=
  sq_nonneg _











theorem normalizedSelbergMajorant_nonneg
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : 0 ≤ cχ)
    {R : ℕ} (hR : 1 ≤ R) (W n : ℕ) :
    0 ≤ normalizedSelbergMajorant χ cχ R W n := by
  unfold normalizedSelbergMajorant
  have hlogR : 0 ≤ Real.log (R : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hR)
  exact div_nonneg
    (mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (smoothSelbergWeight_nonneg χ R n))
    (mul_nonneg hcχ hlogR)



end Wikipedia.SzemeredisTheorem

end

section



/-!
# The smooth cutoff instantiated in the Selberg majorant

This file connects `SmoothSieveCutoff` to the previously total divisor-sum
definitions.  The positivity of the cutoff normalizer discharges every
normalization side condition, including the exact value of the majorant on
primes beyond the sieve level.
-/

namespace Wikipedia.SzemeredisTheorem







theorem SmoothSieveCutoff.majorant_nonneg
    (χ : SmoothSieveCutoff) {R : ℕ} (hR : 1 ≤ R)
    (W n : ℕ) :
    0 ≤ χ.majorant R W n :=
  normalizedSelbergMajorant_nonneg χ.toFun
    χ.normalizer_nonneg hR W n













end Wikipedia.SzemeredisTheorem

end

section


/-!
# The global cyclic Selberg majorant

The prime weight is localized to `greenTaoInterval` in order to unwrap a
positive cyclic progression at the end of the proof.  Its transference
majorant does not need the same localization: outside the interval the prime
weight is zero, so any nonnegative majorant is sufficient.

Keeping the smooth Selberg majorant on the whole standard residue system
removes interval indicators from the linear-forms estimate.  This file
defines that global cyclic majorant, proves pointwise domination from the
existing localized theorem, and reindexes every Boolean CFZ subproduct as a
product over its selected subtype.  The latter is the exact interface needed
to apply the generic finite divisor and Fourier expansions to every exponent
tested by `HasLinearFormsCondition`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



theorem SmoothSieveCutoff.cyclicMajorant_nonneg
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 ≤ R) (W b : ℕ) (n : ZMod N) :
    0 ≤ χ.cyclicMajorant R W b n :=
  χ.majorant_nonneg hR W (wTrickedValue W b n)

/-- On the extraction interval the global and localized Selberg majorants
are literally equal. -/
theorem SmoothSieveCutoff.wTrickedMajorant_eq_cyclicMajorant
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    (R W b : ℕ) {n : ZMod N}
    (hn : n.val ∈ greenTaoInterval N) :
    χ.wTrickedMajorant R W b n =
      χ.cyclicMajorant R W b n := by
  simp [SmoothSieveCutoff.wTrickedMajorant,
    Wikipedia.SzemeredisTheorem.wTrickedMajorant,
    SmoothSieveCutoff.cyclicMajorant,
    SmoothSieveCutoff.majorant, hn]

/-- Any pointwise majorization by the localized majorant automatically gives
majorization by the global one.  On the support interval the two agree; off
the interval the localized prime weight vanishes and the global majorant is
nonnegative. -/
theorem wTrickedPrimeWeight_le_cyclicMajorant_of_le_localized
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {α : ℝ} {R W b : ℕ} (hR : 1 ≤ R)
    (hlocalized :
      ∀ n : ZMod N,
        wTrickedPrimeWeight α W b n ≤
          χ.wTrickedMajorant R W b n) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight α W b n ≤
        χ.cyclicMajorant R W b n := by
  intro n
  by_cases hn : n.val ∈ greenTaoInterval N
  · rw [← χ.wTrickedMajorant_eq_cyclicMajorant R W b hn]
    exact hlocalized n
  · rw [wTrickedPrimeWeight]
    simp only [hn, false_and, if_false]
    exact χ.cyclicMajorant_nonneg hR W b n













end Wikipedia.SzemeredisTheorem

end
/-!
# Assembly-facing prime-weight majorization

The pointwise Selberg majorization theorem reduces its substantive case to
two scalar inequalities: the sieve level lies below the represented prime,
and the scaled logarithm of that prime is at most
`log R / χ.normalizer`.

This file derives both inequalities from global bounds that are independent
of the residue `n`.  The remaining eventual parameter argument only has to
establish those four global bounds for `R = sieveLevel k N`.
-/
open Wikipedia.SzemeredisTheorem
open Filter Real

open Wikipedia.SzemeredisTheorem in
/-- The same eventual majorization with the global cyclic Selberg majorant.

This is the assembly-facing version useful for the linear-forms estimate:
the prime weight is still localized for the final unwrapping argument, but
the majorant remains a pure Selberg weight on every residue. -/
theorem solution
    (χ : SmoothSieveCutoff)
    {k W : ℕ} (hk : 3 ≤ k) (hW : 0 < W)
    (b : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N,
      letI : NeZero N := ⟨hN.ne'⟩
      ∀ n : ZMod N,
        wTrickedPrimeWeight
            (primeScale k χ.normalizer) W b n ≤
          χ.cyclicMajorant (sieveLevel k N) W b n := by
  obtain ⟨N₀, hlocalized⟩ :=
    exists_threshold_wTrickedPrimeWeight_le_sieveMajorant
      χ hk hW b
  obtain ⟨N₁, hlevel⟩ :=
    eventually_atTop.1 (eventually_two_le_sieveLevel hk)
  refine ⟨max N₀ N₁, ?_⟩
  intro N hNlarge hNpos
  let : NeZero N := ⟨hNpos.ne'⟩
  apply
    wTrickedPrimeWeight_le_cyclicMajorant_of_le_localized
      χ
      (by
        have htwo : 2 ≤ sieveLevel k N :=
          hlevel N ((le_max_right N₀ N₁).trans hNlarge)
        omega)
  exact
    hlocalized N ((le_max_left N₀ N₁).trans hNlarge)
      hNpos
