-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_CumulativeLcmTransfer
-- name    : ErdosProblems_Erdos243_CumulativeLcmTransfer
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:27:42.136905+00:00
-- url     : https://prove2.me/theorems/18ac0a17-05d5-478a-8719-852df99cd59f
-- title:
--   LCM transfer coordinates
-- statement:
--   With L_n and accumulated overlap M_n defined by the preceding LCM recurrences, defines g_n=gcd(L_n,a_n), U_n=C_n/M_n by natural-number division, V_n=L_n-(a_n-1)U_n in the integers, and the number of indices with g_n>1. Exact division and the recurrence for U are proved under the separately stated denominator and tail recurrence hypotheses; they are not true for arbitrary independent choices of C and D.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/CumulativeLcmTransfer.lean#L1-L530
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_CumulativeLcmTransfer is the versioned native alias of original module ErdosProblems.Erdos243.CumulativeLcmTransfer.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_GlobalLcmHeight
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős #243: cumulative-LCM transfer

`GlobalLcmHeight.lean` introduces the cumulative LCM `Λₙ`, the product-cleared
denominator scale `Dₙ`, the overlap debt `Mₙ`, and the exact relocation identity
`Mₙ Λₙ = Dₙ`.  What it does not supply is the transfer of that identity to the
*numerator*: whether the irreversible overlap payments recorded in `Mₙ` are
actually carried by the reciprocal-tail state `Cₙ`.

This module lands that transfer and its consequences.

* `cumulativeOverlapDebt_dvd_tailNumerator`: `Mₙ ∣ Cₙ`, by induction using only
  `ρₙ ∣ Λₙ` and `ρₙ ∣ aₙ`.  No positivity hypothesis is needed: `Mₙ₊₁` divides
  `aₙ Cₙ` and `Dₙ` separately, hence their difference.
* `cumulativeOverlapDebt_dvd_centeredState`: `Mₙ ∣ Eₙ` over `ℤ`.
* The LCM-normalised state `Uₙ = Cₙ / Mₙ`, `Vₙ = Λₙ - (aₙ - 1) Uₙ`, with the
  exact reconstruction `Mₙ Uₙ = Cₙ`, `Mₙ Vₙ = Eₙ` and the exact recurrence
  `ρₙ Uₙ₊₁ = Uₙ - Vₙ`.  `Vₙ` is *defined* by the centred formula, so the
  centring identity is definitional and no truncated division appears in any
  equation.
* `pow_lcmNonFreshCount_le_overlapDebt`: the division-free freshness budget
  `2^{#{j<n : ρⱼ > 1}} ≤ Mₙ`, hence `≤ Cₙ`.  This is the exact finite
  inequality behind "LCM freshness has density one".
* `lcmFresh_pairwiseCoprime`: multipliers at LCM-fresh indices are coprime to
  every earlier multiplier.
* `lcmNonFreshCount_sublinear_of_subexponential` and its exact-orbit
  specialisation: subexponential tail growth makes the non-fresh count
  sublinear in the division-free sense `K · count < n`.
* `no_lcmState_of_freshBlock`: the finite shifted-CRT first-crossing
  contradiction for the LCM-normalised state.  Unlike
  `LcmCriticalBoundary.no_boundedNegative_lcmState_of_oldPrimeSupply` the
  moduli are *whole numbers*, not primes, the block is finite, and the rise
  bound is only required below twice the block product.

Nothing here settles Erdős #243.  The analytic input that would place a block
of `B` pairwise-coprime old moduli all exceeding `B` by time `B + o(B)` is not
formalised.
-/

namespace ErdosProblems.Erdos243

/-! ## The cumulative LCM chain -/







/-- The cumulative LCM is positive on any orbit with positive seed and
positive multipliers. -/
theorem cumulativeDigitLcm_pos {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n) :
    ∀ n, 0 < cumulativeDigitLcm q a n := by
  intro n
  induction n with
  | zero => exact hq
  | succ n ih => exact Nat.lcm_pos ih (ha n)

/-! ## The overlap multiplier -/

/-- The one-step LCM overlap payment `ρₙ = gcd(Λₙ, aₙ)`. -/
def lcmOverlap (q : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.gcd (cumulativeDigitLcm q a n) (a n)



theorem cumulativeOverlapDebt_succ' (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeOverlapDebt q a (n + 1) =
      cumulativeOverlapDebt q a n * lcmOverlap q a n := rfl

theorem lcmOverlap_dvd_lcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    lcmOverlap q a n ∣ cumulativeDigitLcm q a n :=
  Nat.gcd_dvd_left _ _

theorem lcmOverlap_dvd_digit (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    lcmOverlap q a n ∣ a n :=
  Nat.gcd_dvd_right _ _

theorem lcmOverlap_pos {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n) (n : ℕ) :
    0 < lcmOverlap q a n :=
  Nat.gcd_pos_of_pos_left (a n) (cumulativeDigitLcm_pos hq ha n)

theorem cumulativeOverlapDebt_pos {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n) :
    ∀ n, 0 < cumulativeOverlapDebt q a n := by
  intro n
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
      rw [cumulativeOverlapDebt_succ']
      exact Nat.mul_pos ih (lcmOverlap_pos hq ha n)



/-! ## The keystone: overlap debt divides the tail numerator -/

/-- **Exact overlap-debt divisibility.**  Along any exact reciprocal-tail orbit
`Cₙ₊₁ + Dₙ = aₙ Cₙ` whose denominator is the product-cleared scale, the
cumulative overlap debt divides the numerator state: `Mₙ ∣ Cₙ`.

This is the transfer of the relocation identity `Mₙ Λₙ = Dₙ` from the
denominator to the numerator.  The induction needs no positivity, and no
subtraction inside `ℕ` occurs anywhere in it: `Mₙ₊₁ = Mₙ ρₙ` divides `aₙ Cₙ`
and `Dₙ` separately — `ρₙ ∣ aₙ` gives the first, `ρₙ ∣ Λₙ` together with
`Mₙ Λₙ = Dₙ` gives the second — so the additive update `Cₙ₊₁ + Dₙ = aₙ Cₙ`
transfers the divisibility directly.  The base case is `M₀ = 1`. -/
theorem cumulativeOverlapDebt_dvd_tailNumerator
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n) :
    ∀ n, cumulativeOverlapDebt q a n ∣ C n := by
  intro n
  induction n with
  | zero => exact one_dvd _
  | succ n ih =>
      have hMD : cumulativeOverlapDebt q a (n + 1) ∣ D n := by
        rw [hD n, ← cumulativeOverlapDebt_mul_lcm_eq_productScale q a n,
          cumulativeOverlapDebt_succ']
        exact Nat.mul_dvd_mul_left _ (lcmOverlap_dvd_lcm q a n)
      have hMaC : cumulativeOverlapDebt q a (n + 1) ∣ a n * C n := by
        have hprod :
            cumulativeOverlapDebt q a n * lcmOverlap q a n ∣ C n * a n :=
          mul_dvd_mul ih (lcmOverlap_dvd_digit q a n)
        rw [cumulativeOverlapDebt_succ', Nat.mul_comm (a n) (C n)]
        exact hprod
      have htotal : cumulativeOverlapDebt q a (n + 1) ∣ C (n + 1) + D n := by
        rw [hstep n]
        exact hMaC
      exact (Nat.dvd_add_iff_left hMD).mpr htotal



/-! ## The LCM-normalised state and its exact system -/

/-- The LCM-normalised numerator `Uₙ = Cₙ / Mₙ`.  Every theorem below consumes
it only through the exact reconstruction `Mₙ Uₙ = Cₙ`, never through the
truncated quotient. -/
def lcmLiftedNumerator (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℕ :=
  C n / cumulativeOverlapDebt q a n

/-- The LCM-normalised centred digit `Vₙ = Λₙ - (aₙ - 1) Uₙ`, defined by the
centred formula so that the centring identity is definitional.  That it really
is `Eₙ / Mₙ` is the content of `lcmLiftedDigit_mul_overlapDebt`. -/
def lcmLiftedDigit (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℤ :=
  (cumulativeDigitLcm q a n : ℤ) -
    ((a n : ℤ) - 1) * (lcmLiftedNumerator q a C n : ℤ)

/-- Exact reconstruction of the numerator from its LCM-normalised form. -/
theorem lcmLiftedNumerator_spec
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    cumulativeOverlapDebt q a n * lcmLiftedNumerator q a C n = C n :=
  Nat.mul_div_cancel' (cumulativeOverlapDebt_dvd_tailNumerator q a C D hD hstep n)

/-- Integer form of the reconstruction. -/
theorem lcmLiftedNumerator_cast_spec
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    (cumulativeOverlapDebt q a n : ℤ) * (lcmLiftedNumerator q a C n : ℤ) =
      (C n : ℤ) := by
  exact_mod_cast lcmLiftedNumerator_spec q a C D hD hstep n



/-- The LCM-normalised digit really is the centred error divided by the
overlap debt: `Mₙ Vₙ = Eₙ`, exactly. -/
theorem lcmLiftedDigit_mul_overlapDebt
    (q : ℕ) (a C D : ℕ → ℕ)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    (cumulativeOverlapDebt q a n : ℤ) * lcmLiftedDigit q a C n =
      centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
  have hU := lcmLiftedNumerator_cast_spec q a C D hD hstep n
  have hDZ :
      (cumulativeOverlapDebt q a n : ℤ) * (cumulativeDigitLcm q a n : ℤ) =
        (D n : ℤ) := by
    rw [hD n, ← cumulativeOverlapDebt_mul_lcm_eq_productScale q a n]
    push_cast
    ring
  simp only [lcmLiftedDigit, centeredState]
  calc
    (cumulativeOverlapDebt q a n : ℤ) *
          ((cumulativeDigitLcm q a n : ℤ) -
            ((a n : ℤ) - 1) * (lcmLiftedNumerator q a C n : ℤ)) =
        (cumulativeOverlapDebt q a n : ℤ) * (cumulativeDigitLcm q a n : ℤ) -
          ((a n : ℤ) - 1) *
            ((cumulativeOverlapDebt q a n : ℤ) *
              (lcmLiftedNumerator q a C n : ℤ)) := by ring
    _ = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ) := by rw [hDZ, hU]

/-- **The exact LCM-normalised recurrence** `ρₙ Uₙ₊₁ = Uₙ - Vₙ`.  This is the
pseudo-Euclidean update of `globalLcm_numerator_update` realised on the actual
cumulative-LCM coordinates, with the overlap payment `ρₙ` charged explicitly. -/
theorem lcmLifted_step
    {q : ℕ} {a : ℕ → ℕ} (C D : ℕ → ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hD : ∀ n, D n = digitProductScale q a n)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (n : ℕ) :
    (lcmOverlap q a n : ℤ) * (lcmLiftedNumerator q a C (n + 1) : ℤ) =
      (lcmLiftedNumerator q a C n : ℤ) - lcmLiftedDigit q a C n := by
  have hMpos : (0 : ℤ) < (cumulativeOverlapDebt q a n : ℤ) := by
    exact_mod_cast cumulativeOverlapDebt_pos hq ha n
  refine mul_left_cancel₀ (ne_of_gt hMpos) ?_
  have hUn := lcmLiftedNumerator_cast_spec q a C D hD hstep n
  have hUsucc := lcmLiftedNumerator_cast_spec q a C D hD hstep (n + 1)
  have hV := lcmLiftedDigit_mul_overlapDebt q a C D hD hstep n
  have hMsucc :
      (cumulativeOverlapDebt q a (n + 1) : ℤ) =
        (cumulativeOverlapDebt q a n : ℤ) * (lcmOverlap q a n : ℤ) := by
    rw [cumulativeOverlapDebt_succ']
    push_cast
    ring
  have hstepZ : (C (n + 1) : ℤ) + (D n : ℤ) = (a n : ℤ) * (C n : ℤ) := by
    exact_mod_cast hstep n
  simp only [centeredState] at hV
  calc
    (cumulativeOverlapDebt q a n : ℤ) *
          ((lcmOverlap q a n : ℤ) * (lcmLiftedNumerator q a C (n + 1) : ℤ)) =
        ((cumulativeOverlapDebt q a n : ℤ) * (lcmOverlap q a n : ℤ)) *
          (lcmLiftedNumerator q a C (n + 1) : ℤ) := by ring
    _ = (cumulativeOverlapDebt q a (n + 1) : ℤ) *
          (lcmLiftedNumerator q a C (n + 1) : ℤ) := by rw [hMsucc]
    _ = (C (n + 1) : ℤ) := hUsucc
    _ = (C n : ℤ) - ((D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ)) := by
        linarith [hstepZ]
    _ = (cumulativeOverlapDebt q a n : ℤ) * (lcmLiftedNumerator q a C n : ℤ) -
          (cumulativeOverlapDebt q a n : ℤ) * lcmLiftedDigit q a C n := by
        rw [hUn, hV]
    _ = (cumulativeOverlapDebt q a n : ℤ) *
          ((lcmLiftedNumerator q a C n : ℤ) - lcmLiftedDigit q a C n) := by ring

/-! ## The freshness budget -/

/-- Number of LCM-non-fresh steps strictly before `n`: the indices where the
current multiplier shares a factor with the accumulated LCM. -/
def lcmNonFreshCount (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => lcmNonFreshCount q a n + if 1 < lcmOverlap q a n then 1 else 0

@[simp]
theorem lcmNonFreshCount_zero (q : ℕ) (a : ℕ → ℕ) :
    lcmNonFreshCount q a 0 = 0 := rfl

@[simp]
theorem lcmNonFreshCount_succ (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    lcmNonFreshCount q a (n + 1) =
      lcmNonFreshCount q a n + if 1 < lcmOverlap q a n then 1 else 0 := rfl





/-! ## Coprimality of fresh multipliers -/





/-! ## Sublinearity of the non-fresh count -/





/-! ## The shifted-CRT first-crossing barrier for the normalised state -/





end ErdosProblems.Erdos243


