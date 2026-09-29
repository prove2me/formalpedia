-- Prove2me | solution 1 for CyclicTypeChannel.Ipair_prime_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:47:36.776248+00:00
-- url     : https://prove2.me/submissions/c7e2f0d3-87a7-4317-b2f5-8b571da2dc62

-- Sol generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
import Theorems.Thm_CyclicTypeChannel_Ipair_prime
import Theorems.Thm_CyclicTypeChannel_logb_sub_logb_le
/-
# The prime cyclic order: a closed form for the type-pair channel

The exact-value files compute the type-pair channel `Ipair n` for a finite list of
cyclic orders.  This file closes the *prime* case in complete generality: for
every prime `p` the channel of the cyclic order `C p` is

  `Ipair p = log₂ p - (p-1)(2p-1)/p² · log₂ (p-1) + (p-1)(p-2)/p² · log₂ (p-2)`.

(`Ipair_prime`; the two exact values `Ipair 3` and `Ipair 5` recorded in
`CyclicTypeChannelCRT.lean` are the instances `p = 3, 5`.)

Two consequences:

* `Ipair_prime_lt_one`: every **odd** prime order is *strictly below* the one-bit
  binary-fork cap, so among prime cyclic orders the cap is attained exactly at
  `p = 2` (`Ipair_prime_eq_one_iff`).  This upgrades the isolated computations
  `Ipair 3 < 1`, `Ipair 5 < 1` to an infinite statement and shows that the
  above-cap phenomenon of `C₄, C₆, C₁₀, C₁₂, C₁₆` is genuinely a *composite*
  phenomenon: a prime cyclic order has only two splitting types, and its fork is
  exactly the binary fork that papers 72–74 capped.
* `above_cap_imp_not_prime`: breaking the cap forces the cyclic order to be
  composite.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. The splitting type of a prime cyclic order -/





/-! ## 2. The three fibres in the CyclicTypeChannel.box -/











/-! ## 3. The pair entropy -/



/-! ## 4. The conditional entropy -/











/-! ### The nonzero fibres -/









/-! ## 5. Consequences: the cap among prime orders -/







/-! ## 6. Cross-checks against the enumerated values

`Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
prime formula is an independent check of the closed form. -/




open CyclicTypeChannel in
theorem solution{p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Ipair p ≤ (Real.logb 2 (p : ℝ) + 3 * (p : ℝ)) / (p : ℝ) ^ 2 := by
  have hp3 : 3 ≤ p := by
    have h := hp.two_le
    rcases eq_or_lt_of_le h with h' | h'
    · exact absurd h'.symm hp2
    · omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  set L := Real.logb 2 (p : ℝ) with hL
  set L1 := Real.logb 2 ((p : ℝ) - 1) with hL1
  set L2 := Real.logb 2 ((p : ℝ) - 2) with hL2
  set A := ((p : ℝ) - 1) * (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2 with hA
  set B := ((p : ℝ) - 1) * ((p : ℝ) - 2) / (p : ℝ) ^ 2 with hB
  have hkey : L - L1 ≤ 1 / (((p : ℝ) - 1) * Real.log 2) := by
    have h := logb_sub_logb_le (x := (p : ℝ) - 1) (by linarith)
    have e : (p : ℝ) - 1 + 1 = (p : ℝ) := by ring
    rw [e] at h
    exact h
  have hApos : 0 ≤ A := by
    rw [hA]; apply div_nonneg _ (by positivity); nlinarith
  have hBpos : 0 ≤ B := by
    rw [hB]; apply div_nonneg _ (by positivity); nlinarith
  have hL2le : L2 ≤ L := by
    rw [hL2, hL]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hdecomp : Ipair p = L * (1 - A + B) + A * (L - L1) - B * (L - L2) := by
    rw [Ipair_prime hp, hA, hB, hL, hL1, hL2]
    field_simp
    ring
  have hcoeff : 1 - A + B = 1 / (p : ℝ) ^ 2 := by
    rw [hA, hB]; field_simp; ring
  have hne1' : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hne2' : (p : ℝ) ≠ 0 := by linarith
  have hne3' : Real.log 2 ≠ 0 := by linarith
  have hstep1 : A * (L - L1) ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
    calc A * (L - L1) ≤ A * (1 / (((p : ℝ) - 1) * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hkey hApos
      _ = (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
          rw [hA]; field_simp
  have hstep2 : 0 ≤ B * (L - L2) := mul_nonneg hBpos (by linarith)
  have hbound : (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) ≤ 3 * (p : ℝ) / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hcube : (0 : ℝ) < (p : ℝ) ^ 3 := by positivity
    have hmul : (p : ℝ) ^ 3 * 0.6931471803 < (p : ℝ) ^ 3 * Real.log 2 :=
      mul_lt_mul_of_pos_left hlog2 hcube
    nlinarith [hmul, hcube]
  have hcollect : L / (p : ℝ) ^ 2 + 3 * (p : ℝ) / (p : ℝ) ^ 2
      = (L + 3 * (p : ℝ)) / (p : ℝ) ^ 2 := by
    field_simp
  have hLdiv : L * (1 / (p : ℝ) ^ 2) = L / (p : ℝ) ^ 2 := by ring
  rw [hdecomp, hcoeff]
  linarith [hstep1, hstep2, hbound, hcollect, hLdiv]
