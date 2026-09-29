-- Prove2me | solution 1 for CyclicTypeChannel.Ipair_prime_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:49:06.195931+00:00
-- url     : https://prove2.me/submissions/494ebe02-cce8-46fa-a39d-d17f4184541c

-- Sol generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
import Theorems.Thm_CyclicTypeChannel_Ipair_prime
import Theorems.Thm_CyclicTypeChannel_lb_three_lt
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


/-- `log₂ p ≤ p`. -/
lemma logb_two_le_self {p : ℕ} (hp : 0 < p) : Real.logb 2 (p : ℝ) ≤ (p : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (p : ℝ) ≤ 2 ^ p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  have h2 : Real.log (p : ℝ) ≤ Real.log ((2 : ℝ) ^ p) :=
    Real.log_le_log (by exact_mod_cast hp) h1
  rw [Real.log_pow] at h2
  rw [Real.logb, div_le_iff₀ hlog2]
  calc Real.log (p : ℝ) ≤ (p : ℕ) * Real.log 2 := h2
    _ = (p : ℝ) * Real.log 2 := by ring





/-! ## 6. Cross-checks against the enumerated values

`Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
prime formula is an independent check of the closed form. -/




open CyclicTypeChannel in
theorem solution{p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Ipair p < 1 := by
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
  -- the first-order bound on the marginal gap
  have hkey : L - L1 ≤ 1 / (((p : ℝ) - 1) * Real.log 2) := by
    have h := logb_sub_logb_le (x := (p : ℝ) - 1) (by linarith)
    have e : (p : ℝ) - 1 + 1 = (p : ℝ) := by ring
    rw [e] at h
    exact h
  have hApos : 0 ≤ A := by
    rw [hA]
    apply div_nonneg _ (by positivity)
    nlinarith
  have hBpos : 0 ≤ B := by
    rw [hB]
    apply div_nonneg _ (by positivity)
    nlinarith
  have hL2le : L2 ≤ L := by
    rw [hL2, hL]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  -- the algebraic decomposition of the channel
  have hdecomp : Ipair p = L * (1 - A + B) + A * (L - L1) - B * (L - L2) := by
    rw [Ipair_prime hp, hA, hB, hL, hL1, hL2]
    field_simp
    ring
  have hcoeff : 1 - A + B = 1 / (p : ℝ) ^ 2 := by
    rw [hA, hB]
    field_simp
    ring
  have hne1' : ((p : ℝ) - 1) ≠ 0 := by linarith
  have hne2' : (p : ℝ) ≠ 0 := by linarith
  have hne3' : Real.log 2 ≠ 0 := by linarith
  have hstep1 : A * (L - L1) ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
    calc A * (L - L1) ≤ A * (1 / (((p : ℝ) - 1) * Real.log 2)) :=
          mul_le_mul_of_nonneg_left hkey hApos
      _ = (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
          rw [hA]; field_simp
  have hstep2 : 0 ≤ B * (L - L2) := mul_nonneg hBpos (by linarith)
  have hIle : Ipair p ≤ L / (p : ℝ) ^ 2 + (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) := by
    rw [hdecomp, hcoeff]
    have : L * (1 / (p : ℝ) ^ 2) = L / (p : ℝ) ^ 2 := by ring
    linarith [hstep1, hstep2, this]
  -- the numerical bound
  have hnum : L / (p : ℝ) ^ 2 + (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2) < 1 := by
    have hcollect : L / (p : ℝ) ^ 2 + (2 * (p : ℝ) - 1) / ((p : ℝ) ^ 2 * Real.log 2)
        = (L + (2 * (p : ℝ) - 1) / Real.log 2) / (p : ℝ) ^ 2 := by
      field_simp
    rw [hcollect, div_lt_one (by positivity)]
    have hq : (2 * (p : ℝ) - 1) / Real.log 2 < (2 * (p : ℝ) - 1) / 0.6931471803 :=
      div_lt_div_of_pos_left (by linarith) (by norm_num) hlog2
    rcases eq_or_lt_of_le hp3 with h3 | h3
    · -- `p = 3`
      have hp3' : p = 3 := h3.symm
      subst hp3'
      have hLlt : L < 8 / 5 := by
        rw [hL]
        have : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
        rw [this]
        exact lb_three_lt
      have hcast3 : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
      rw [hcast3] at hq ⊢
      norm_num at hq ⊢
      linarith
    · -- `p ≥ 4`
      have hp4 : (4 : ℝ) ≤ (p : ℝ) := by
        have : 4 ≤ p := by omega
        exact_mod_cast this
      have hLle : L ≤ (p : ℝ) := by rw [hL]; exact logb_two_le_self hp.pos
      have hlin : (2 * (p : ℝ) - 1) / 0.6931471803 ≤ 2.8854 * (p : ℝ) - 1.4427 := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith
      nlinarith
  linarith
