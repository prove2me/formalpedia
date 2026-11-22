-- Prove2me | solution 1 for Erdos390.WholePaper.roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:48:52.603993+00:00
-- url     : https://prove2.me/submissions/028894ca-c203-4627-b699-ed64b839b5b6

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_008

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/





































private theorem mem_smooth_succ_not_smooth_iff_dvd {p m : ℕ}
    (hp : p.Prime) (hm : m ∈ Nat.smoothNumbers (p + 1)) :
    m ∉ Nat.smoothNumbers p ↔ p ∣ m := by
  rw [Nat.mem_smoothNumbers'] at hm
  constructor
  · intro hnot
    by_contra hpdvd
    apply hnot
    rw [Nat.mem_smoothNumbers']
    intro q hq hqdiv
    have hqsucc : q < p + 1 := hm q hq hqdiv
    have hqne : q ≠ p := by
      intro hqp
      exact hpdvd (hqp ▸ hqdiv)
    omega
  · intro hpdiv hsmooth
    rw [Nat.mem_smoothNumbers'] at hsmooth
    exact (Nat.lt_irrefl p) (hsmooth p hp hpdiv)

theorem primeMultipleCell_card (X : ℕ) {p : ℕ} (hp : p.Prime) :
    (primeMultipleCell X p).card = friableCount (X / p) p := by
  classical
  apply Finset.card_bij (fun m _ => m / p)
  · intro m hm
    rw [primeMultipleCell, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo] at hm
    rw [Nat.mem_smoothNumbersUpTo]
    refine ⟨?_, Nat.mem_smoothNumbers_of_dvd hm.1.2 (Nat.div_dvd_of_dvd hm.2)⟩
    apply (Nat.le_div_iff_mul_le hp.pos).mpr
    simpa [Nat.div_mul_cancel hm.2] using hm.1.1
  · intro m₁ hm₁ m₂ hm₂ heq
    rw [primeMultipleCell, Finset.mem_filter] at hm₁ hm₂
    calc
      m₁ = m₁ / p * p := (Nat.div_mul_cancel hm₁.2).symm
      _ = m₂ / p * p := by rw [heq]
      _ = m₂ := Nat.div_mul_cancel hm₂.2
  · intro k hk
    rw [Nat.mem_smoothNumbersUpTo] at hk
    refine ⟨k * p, ?_, ?_⟩
    · rw [primeMultipleCell, Finset.mem_filter,
        Nat.mem_smoothNumbersUpTo]
      refine ⟨⟨?_, Nat.mul_mem_smoothNumbers hk.2 ?_⟩, by simp⟩
      · exact (Nat.le_div_iff_mul_le hp.pos).mp hk.1
      · exact Nat.mem_smoothNumbers_of_lt hp.pos (by omega)
    · exact Nat.mul_div_left k hp.pos

/-- Exact one-prime Buchstab recursion.  The first term excludes `p`; the
second term divides the newly admitted multiples of `p` by `p`.  Repeatedly
applying this identity is the discrete arithmetic induction underlying the
finite-range de Bruijn argument. -/
theorem friableCount_prime_step (X : ℕ) {p : ℕ} (hp : p.Prime) :
    friableCount X p =
      friableCount X (p - 1) + friableCount (X / p) p := by
  classical
  let A := Nat.smoothNumbersUpTo X (p + 1)
  let P : ℕ → Prop := fun m => m ∈ Nat.smoothNumbers p
  have hpartition := Finset.card_filter_add_card_filter_not (s := A) P
  have hbelow : A.filter P = Nat.smoothNumbersUpTo X p := by
    ext m
    simp only [A, P, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hmX, hm⟩, hmp⟩
      exact ⟨hmX, hmp⟩
    · rintro ⟨hmX, hmp⟩
      exact ⟨⟨hmX, Nat.smoothNumbers_mono (by omega) hmp⟩, hmp⟩
  have hnew : A.filter (fun m => ¬P m) = primeMultipleCell X p := by
    ext m
    simp only [A, P, primeMultipleCell, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hmX, hm⟩, hn⟩
      exact ⟨⟨hmX, hm⟩, (mem_smooth_succ_not_smooth_iff_dvd hp hm).mp hn⟩
    · rintro ⟨⟨hmX, hm⟩, hpdiv⟩
      exact ⟨⟨hmX, hm⟩, (mem_smooth_succ_not_smooth_iff_dvd hp hm).mpr hpdiv⟩
  rw [hbelow, hnew, primeMultipleCell_card X hp] at hpartition
  have hpone : 1 ≤ p := hp.one_le
  simpa [friableCount, Nat.sub_add_cancel hpone, A] using hpartition.symm

/-- At a composite cutoff no new smooth numbers appear. -/
theorem friableCount_composite_step (X : ℕ) {k : ℕ} (hk : ¬k.Prime) :
    friableCount X k = friableCount X (k - 1) := by
  by_cases hk0 : k = 0
  · subst k
    simp [friableCount]
  have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  rw [friableCount, friableCount, Nat.sub_add_cancel hkone]
  unfold Nat.smoothNumbersUpTo
  congr 1
  ext m
  simp only [Finset.mem_filter, Nat.smoothNumbers_succ hk]

private theorem friableCount_cutoff_zero {X : ℕ} (hX : 0 < X) :
    friableCount X 0 = 1 := by
  have hset : Nat.smoothNumbersUpTo X 1 = {1} := by
    ext m
    rw [Nat.mem_smoothNumbersUpTo, Nat.smoothNumbers_one]
    simp only [Set.mem_singleton_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hmX, rfl⟩
      rfl
    · rintro rfl
      exact ⟨hX, rfl⟩
  rw [friableCount, hset]
  simp

/-- Exact largest-prime-factor recursion

`\Psi(X,y) = 1 + \sum_{p \le y} \Psi(\lfloor X/p\rfloor,p)`.

The identity follows here from the one-prime step and therefore does not need
an independently postulated greatest-prime-factor decomposition.  This is the
finite recurrence to which prime Stieltjes summation is applied in the
de Bruijn induction. -/
theorem friableCount_largest_prime (X y : ℕ) (hX : 0 < X) :
    friableCount X y =
      1 + ∑ p ∈ (y + 1).primesBelow, friableCount (X / p) p := by
  induction y with
  | zero =>
      rw [friableCount_cutoff_zero hX]
      simp [Nat.primesBelow]
  | succ y ih =>
      by_cases hp : (y + 1).Prime
      · rw [friableCount_prime_step X hp]
        have hsub : y + 1 - 1 = y := by omega
        have hprimes : (y + 1 + 1).primesBelow =
            insert (y + 1) (y + 1).primesBelow := by
          rw [Nat.primesBelow_succ, if_pos hp]
        rw [hsub, ih, hprimes,
          Finset.sum_insert (Nat.notMem_primesBelow (y + 1))]
        omega
      · rw [friableCount_composite_step X hp]
        have hsub : y + 1 - 1 = y := by omega
        have hprimes : (y + 1 + 1).primesBelow = (y + 1).primesBelow := by
          rw [Nat.primesBelow_succ, if_neg hp]
        rw [hsub, ih, hprimes]

/-- Truncated largest-prime recursion.  This is the induction-friendly form:
choosing `z` so that `log X / log z` is an integer puts the first term on the
previous Dickman step, while every quotient in the prime interval has a
strictly smaller Dickman coordinate. -/
theorem friableCount_prime_interval (X : ℕ) {z y : ℕ} (hX : 0 < X)
    (hzy : z ≤ y) :
    friableCount X y = friableCount X z +
      ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        friableCount (X / p) p := by
  have hsubset : (z + 1).primesBelow ⊆ (y + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum :
      (∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          friableCount (X / p) p) +
        ∑ p ∈ (z + 1).primesBelow, friableCount (X / p) p =
          ∑ p ∈ (y + 1).primesBelow, friableCount (X / p) p := by
    simpa only using
      (Finset.sum_sdiff (f := fun p => friableCount (X / p) p) hsubset)
  rw [friableCount_largest_prime X y hX,
    friableCount_largest_prime X z hX]
  omega

/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/





























































end Erdos390.Full.FriableAsymptotic

end

/- Source module: Erdos390.WholePaper.RoughFriableFaceInduction -/
section


/-!
# Method of steps for local friable residual regularity

This file pushes the exact reverse-Buchstab finite-difference identity through
the five Dickman faces used in Section 6.  The induction hypothesis is always
on the strictly lower quotient coordinate: for `y < p`, division by `p`
changes the face bound from `m + 1` to `m`.

There is one remaining analytic input.  It is stated below as the exact
prime-transition cancellation between the deterministic Dickman defect and
the strictly lower-face quotient residual sum.  It contains no selector,
head, row, feasibility, or target-face residual assertion.  The cumulative
PNT and floor ledgers already available in the library are proved separately,
making precise why an endpoint estimate alone does not settle the local
transition ledger.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Elementary facts about the reverse prime interval -/

theorem roughReversePrimeInterval_prime
    {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    p.Prime := by
  exact Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1

theorem roughReversePrimeInterval_gt_left
    {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    y < p := by
  have hpprime : p.Prime := roughReversePrimeInterval_prime hp
  have hpout := (Finset.mem_sdiff.mp hp).2
  by_contra hnot
  apply hpout
  rw [Nat.mem_primesBelow]
  exact ⟨by omega, hpprime⟩

theorem roughReversePrimeInterval_le_right
    {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    p ≤ Z := by
  have hpbelow := Nat.lt_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  omega

/-! ## Exact continuous/floor decomposition of the main defect -/



















/-! ## Face seminorm and the genuinely local prime ledger -/



















/-! ## The quotient really lies on the lower face -/



/-! ## Literal method-of-steps induction -/











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasEndpointApproximation -/
section


/-!
# A closed inverse-log endpoint approximation for the Saias normal form

The repository already proves a uniform compact estimate for
`Psi(X,y) - X*rho(log X/log y)` and proves separately that
`|G_y-rho| <= 1/log y`.  Combining those two closed estimates gives a
concrete witness for `RoughSaiasEndpointApproximationUpToFive` with rate
`(K+1)/log y`.

This is an unconditional endpoint theorem about the already formalized
normal form.  It is deliberately not described as the sharper cited
Hildebrand--Tenenbaum--Saias estimate: its inverse-log rate is too large for
the final paper-scale absorption.  The exact reverse recurrence at the end
of this file isolates the normal-form prime-sum defect whose sharper control
would supply that missing gain.  The final section makes that claim precise:
an inverse-log-square bound for this explicit defect, together with the
already proved prime contraction, conditionally gives the paper-absorbable
endpoint rate `10*C/log(y)^2`.  Thus the coarse closed witness and the sole
sharp analytic input have different names and cannot be confused downstream.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Named witnesses from the closed Dickman endpoint theorem -/











/-! ## Identification with the formal normal form -/



/-! ## Closed endpoint envelope -/





/-! ## Exact reverse recurrence for the normal-form error -/



/-- Exact reverse recurrence: every counting term has disappeared except
for strictly smaller quotient endpoint errors.  Thus a sharp bound for the
explicit normal-form defect is the non-circular analytic input needed for a
stronger endpoint rate. -/
theorem roughSaiasEndpointError_reverseRecurrence
    {X y Z : ℕ} (hX : 0 < X) (hyZ : y ≤ Z) :
    roughSaiasEndpointError X y =
      roughSaiasEndpointError X Z -
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughSaiasEndpointError (X / p) p +
        roughSaiasReverseNormalFormDefect X y Z := by
  have hrec := FriableAsymptotic.friableCount_prime_interval X hX hyZ
  have hrecReal := congrArg (fun n : ℕ => (n : ℝ)) hrec
  simp only [Nat.cast_add, Nat.cast_sum] at hrecReal
  unfold roughSaiasEndpointError roughSaiasReverseNormalFormDefect
  rw [Finset.sum_sub_distrib]
  dsimp only [roughReversePrimeInterval] at hrecReal ⊢
  linarith

/-- With the reverse cap at the endpoint, the top error is exactly zero. -/
theorem roughSaiasEndpointError_reverseRecurrence_top
    {X y : ℕ} (hX2 : 2 ≤ X) (hyX : y ≤ X) :
    roughSaiasEndpointError X y =
      roughSaiasReverseNormalFormDefect X y X -
        ∑ p ∈ roughReversePrimeInterval y X,
          roughSaiasEndpointError (X / p) p := by
  have hrec := roughSaiasEndpointError_reverseRecurrence
    (X := X) (y := y) (Z := X) (by omega) hyX
  have htop : roughSaiasEndpointError X X = 0 :=
    roughSaiasEndpointError_initial (by omega) (by omega) le_rfl
  rw [hrec, htop]
  ring

/-! ## The sole sharp analytic input and its endpoint consequence -/





theorem roughSaiasPrimeInvLogContraction_bound
    {y X : ℕ} (hY : roughSaiasPrimeInvLogContractionCutoff ≤ y)
    (hyX : y < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    FriableAsymptotic.primeInvLogSum y X ≤
      9 / (10 * Real.log (y : ℝ)) :=
  (Classical.choose_spec
    FriableAsymptotic.exists_primeInvLogSum_contraction_threshold)
    hY hyX hlog



/-- The existing reciprocal-log contraction automatically contracts the
squared reciprocal-log kernel: on the prime interval `p>y`, the additional
factor `1/log p` is at most `1/log y`. -/
theorem roughSaiasPrimeInvLogSqSum_contraction
    {y X : ℕ} (hY : roughSaiasPrimeInvLogContractionCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyX : y < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    roughSaiasPrimeInvLogSqSum y X ≤
      9 / (10 * Real.log (y : ℝ) ^ 2) := by
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcontract := roughSaiasPrimeInvLogContraction_bound hY hyX hlog
  have hcompare : roughSaiasPrimeInvLogSqSum y X ≤
      (1 / Real.log (y : ℝ)) *
        FriableAsymptotic.primeInvLogSum y X := by
    unfold roughSaiasPrimeInvLogSqSum
      FriableAsymptotic.primeInvLogSum
    dsimp only [roughReversePrimeInterval]
    calc
      (∑ p ∈ (X + 1).primesBelow \ (y + 1).primesBelow,
          1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)) ≤
        ∑ p ∈ (X + 1).primesBelow \ (y + 1).primesBelow,
          (1 / Real.log (y : ℝ)) *
            (1 / ((p : ℝ) * Real.log (p : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpprime : p.Prime :=
            Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
          have hyp : y < p := by
            have hpout := (Finset.mem_sdiff.mp hp).2
            by_contra hnot
            apply hpout
            rw [Nat.mem_primesBelow]
            exact ⟨by omega, hpprime⟩
          have hlogp : 0 < Real.log (p : ℝ) :=
            Real.log_pos (by exact_mod_cast hpprime.one_lt)
          have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
          have hinv : 1 / Real.log (p : ℝ) ≤
              1 / Real.log (y : ℝ) :=
            one_div_le_one_div_of_le hlogy hlogyp
          calc
            1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2) =
                (1 / Real.log (p : ℝ)) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ))) := by
              field_simp
            _ ≤ (1 / Real.log (y : ℝ)) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ))) :=
              mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = (1 / Real.log (y : ℝ)) *
          ∑ p ∈ (X + 1).primesBelow \ (y + 1).primesBelow,
            1 / ((p : ℝ) * Real.log (p : ℝ)) := by
        rw [Finset.mul_sum]
  calc
    roughSaiasPrimeInvLogSqSum y X ≤
        (1 / Real.log (y : ℝ)) *
          FriableAsymptotic.primeInvLogSum y X := hcompare
    _ ≤ (1 / Real.log (y : ℝ)) *
          (9 / (10 * Real.log (y : ℝ))) :=
      mul_le_mul_of_nonneg_left hcontract (by positivity)
    _ = 9 / (10 * Real.log (y : ℝ) ^ 2) := by
      field_simp





/-- A sharp bound for the explicit normal-form prime defect is sufficient
for the paper-absorbable endpoint envelope.  The proof is a genuine strong
induction on `X`: the reverse recurrence reduces every error to `X/p<X`, and
the reciprocal-log-square prime sum contracts by `9/10`.

This is conditional only on
`RoughSaiasReverseNormalFormDefectInvLogSqBound`; it does not use the coarse
inverse-log endpoint theorem above as a sharp input. -/
theorem roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
    {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀) :
    RoughSaiasEndpointApproximationUpToFive
      (roughSaiasInvLogSqEndpointRate C)
      (roughSaiasInvLogSqEndpointCutoff Y₀) := by
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      intro y hY hy2 hX hlog
      have hmax : max Y₀ roughSaiasPrimeInvLogContractionCutoff ≤ y := by
        simpa only [roughSaiasInvLogSqEndpointCutoff] using hY
      have hY₀y : Y₀ ≤ y := (le_max_left _ _).trans hmax
      have hZcy : roughSaiasPrimeInvLogContractionCutoff ≤ y :=
        (le_max_right _ _).trans hmax
      have hlogy : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      by_cases hXy : X ≤ y
      · rw [roughSaiasEndpointError_initial hX (by omega) hXy, abs_zero]
        unfold roughSaiasInvLogSqEndpointRate
        positivity
      · have hyX : y < X := lt_of_not_ge hXy
        have hX2 : 2 ≤ X := hy2.trans hyX.le
        let K : ℝ := 10 * C
        have hK : 0 ≤ K := by
          dsimp only [K]
          positivity
        have hquotient : ∀ p ∈ roughReversePrimeInterval y X,
            |roughSaiasEndpointError (X / p) p| ≤
              K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) ^ 2 := by
          intro p hp
          have hpprime : p.Prime := roughReversePrimeInterval_prime hp
          have hyp : y < p := roughReversePrimeInterval_gt_left hp
          have hpX : p ≤ X := roughReversePrimeInterval_le_right hp
          have hquotPos : 1 ≤ X / p :=
            (Nat.le_div_iff_mul_le hpprime.pos).2 (by simpa using hpX)
          have hquotLt : X / p < X :=
            Nat.div_lt_self hX hpprime.one_lt
          have hlogQuotX : Real.log ((X / p : ℕ) : ℝ) ≤
              Real.log (X : ℝ) := by
            apply Real.log_le_log (by exact_mod_cast hquotPos)
            exact_mod_cast Nat.div_le_self X p
          have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
          have hlogQuot5 : Real.log ((X / p : ℕ) : ℝ) ≤
              5 * Real.log (p : ℝ) :=
            hlogQuotX.trans
              (hlog.trans
                (mul_le_mul_of_nonneg_left hlogyp (by norm_num)))
          have hih := ih (X / p) hquotLt (y := p)
            (hY.trans hyp.le) hpprime.two_le (by omega) hlogQuot5
          calc
            |roughSaiasEndpointError (X / p) p| ≤
                roughSaiasInvLogSqEndpointRate C p *
                  ((X / p : ℕ) : ℝ) := hih
            _ = K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2 := by
              unfold roughSaiasInvLogSqEndpointRate
              dsimp only [K]
              ring
        have hsumAbs :
            |∑ p ∈ roughReversePrimeInterval y X,
                roughSaiasEndpointError (X / p) p| ≤
              ∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2 := by
          calc
            |∑ p ∈ roughReversePrimeInterval y X,
                roughSaiasEndpointError (X / p) p| ≤
              ∑ p ∈ roughReversePrimeInterval y X,
                |roughSaiasEndpointError (X / p) p| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2 := by
              exact Finset.sum_le_sum hquotient
        have hsumScale :
            (∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2) ≤
              K * (X : ℝ) * roughSaiasPrimeInvLogSqSum y X := by
          unfold roughSaiasPrimeInvLogSqSum
          calc
            (∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2) ≤
              ∑ p ∈ roughReversePrimeInterval y X,
                K * (X : ℝ) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)) := by
              apply Finset.sum_le_sum
              intro p hp
              have hpprime : p.Prime := roughReversePrimeInterval_prime hp
              have hlogp : 0 < Real.log (p : ℝ) :=
                Real.log_pos (by exact_mod_cast hpprime.one_lt)
              have hcast : ((X / p : ℕ) : ℝ) ≤
                  (X : ℝ) / (p : ℝ) := Nat.cast_div_le
              calc
                K * ((X / p : ℕ) : ℝ) /
                    Real.log (p : ℝ) ^ 2 ≤
                  K * ((X : ℝ) / (p : ℝ)) /
                    Real.log (p : ℝ) ^ 2 := by
                  exact div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hcast hK)
                    (sq_nonneg _)
                _ = K * (X : ℝ) *
                    (1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)) := by
                  field_simp
            _ = K * (X : ℝ) *
                ∑ p ∈ roughReversePrimeInterval y X,
                  1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2) := by
              rw [Finset.mul_sum]
        have hsqContract : roughSaiasPrimeInvLogSqSum y X ≤
            9 / (10 * Real.log (y : ℝ) ^ 2) :=
          roughSaiasPrimeInvLogSqSum_contraction hZcy hy2 hyX hlog
        have hsumContract :
            (∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2) ≤
              (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) ^ 2 := by
          calc
            _ ≤ K * (X : ℝ) * roughSaiasPrimeInvLogSqSum y X :=
              hsumScale
            _ ≤ K * (X : ℝ) *
                (9 / (10 * Real.log (y : ℝ) ^ 2)) := by
              exact mul_le_mul_of_nonneg_left hsqContract
                (mul_nonneg hK (Nat.cast_nonneg X))
            _ = (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) ^ 2 := by ring
        have hdefectBound :
            |roughSaiasReverseNormalFormDefect X y X| ≤
              C * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
          hdefect hY₀y hy2 hyX hlog
        have hrec := roughSaiasEndpointError_reverseRecurrence_top
          hX2 hyX.le
        rw [hrec]
        calc
          |roughSaiasReverseNormalFormDefect X y X -
              ∑ p ∈ roughReversePrimeInterval y X,
                roughSaiasEndpointError (X / p) p| ≤
            |roughSaiasReverseNormalFormDefect X y X| +
              |∑ p ∈ roughReversePrimeInterval y X,
                roughSaiasEndpointError (X / p) p| := abs_sub _ _
          _ ≤ C * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
              ∑ p ∈ roughReversePrimeInterval y X,
                K * ((X / p : ℕ) : ℝ) /
                  Real.log (p : ℝ) ^ 2 :=
            add_le_add hdefectBound hsumAbs
          _ ≤ C * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
              (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) ^ 2 :=
            add_le_add_right hsumContract _
          _ = roughSaiasInvLogSqEndpointRate C y * (X : ℝ) := by
            unfold roughSaiasInvLogSqEndpointRate
            dsimp only [K]
            ring



end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_029 := by
  exact @Erdos390.WholePaper.roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
