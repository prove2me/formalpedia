-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eventually_log_two_div_four_mul_div_log_le_card
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:03:38.206095+00:00
-- url     : https://prove2.me/submissions/f283e001-a496-42fa-b2d4-b5d05adf056a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_Wikipedia_SzemeredisTheorem_chebyshev_expression_le_card_primesInQuarterInterval

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



namespace Wikipedia.SzemeredisTheorem

open Finset Real
open Filter Asymptotics





















private theorem log_add_one_isLittleO_id :
    (fun x : ℝ ↦ log (x + 1)) =o[atTop]
      (fun x : ℝ ↦ x) := by
  have hlog :
      (fun x : ℝ ↦ log (x + 1)) =o[atTop]
        (fun x : ℝ ↦ x + 1) := by
    simpa only [Function.comp_def, id] using
      Real.isLittleO_log_id_atTop.comp_tendsto
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  apply hlog.trans_isBigO
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith),
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

private theorem sqrt_mul_log_isLittleO_id :
    (fun x : ℝ ↦ √x * log x) =o[atTop]
      (fun x : ℝ ↦ x) := by
  have hlog :
      log =o[atTop] (fun x : ℝ ↦ √x) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (r := (1 / 2 : ℝ)) (by norm_num))
  have hmul :=
    (isBigO_refl (fun x : ℝ ↦ √x) atTop).mul_isLittleO hlog
  refine hmul.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact Real.mul_self_sqrt hx

private theorem quarter_interval_chebyshev_error_isLittleO :
    (fun X : ℕ ↦
      log (X + 1 : ℕ) + 2 * √(X : ℝ) * log X) =o[atTop]
        (fun X : ℕ ↦ (X : ℝ)) := by
  have hlog := log_add_one_isLittleO_id.natCast_atTop
  have hsqrtlog := sqrt_mul_log_isLittleO_id.natCast_atTop
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using
    hlog.add (hsqrtlog.const_mul_left 2)

theorem log_two_div_four_pos : 0 < log (2 : ℝ) / 4 :=
  div_pos (Real.log_pos one_lt_two) (by norm_num)

private theorem eventually_quarter_interval_chebyshev_error :
    ∀ᶠ X : ℕ in atTop,
      log (X + 1 : ℕ) + 2 * √(X : ℝ) * log X ≤
        log 2 / 4 * X := by
  have hbound :=
    quarter_interval_chebyshev_error_isLittleO.bound log_two_div_four_pos
  filter_upwards [hbound, eventually_ge_atTop 1] with X hbound hX
  have hlogSucc : 0 ≤ log ((X + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X + 1 by omega))
  have hlogX : 0 ≤ log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  have herrorNonneg :
      0 ≤ log ((X + 1 : ℕ) : ℝ) +
        2 * √(X : ℝ) * log X := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg herrorNonneg,
    abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) by positivity)] using hbound



end Wikipedia.SzemeredisTheorem

end
open Wikipedia.SzemeredisTheorem
open Finset Real
open Filter Asymptotics

open Wikipedia.SzemeredisTheorem in
/-- Quantitative Chebyshev lower bound for all sufficiently large natural
`X`.  The explicit constant `log 2 / 4` is positive. -/
theorem solution :
    ∀ᶠ X : ℕ in atTop,
      log 2 / 4 * X / log X ≤
        (#(primesInQuarterInterval X) : ℝ) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_quarter_interval_chebyshev_error] with X hX herror
  have hlogX : 0 < log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hX))
  rw [div_le_iff₀ hlogX]
  have hquarter :
      log 4 * ((X / 4 : ℕ) : ℝ) ≤
        log 2 / 2 * X := by
    have hdiv :
        ((X / 4 : ℕ) : ℝ) ≤ (X : ℝ) / 4 :=
      Nat.cast_div_le
    have hlog4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    have hlog2 : 0 ≤ log (2 : ℝ) := (Real.log_pos one_lt_two).le
    nlinarith [mul_le_mul_of_nonneg_left hdiv hlog2]
  have hexplicit :=
    chebyshev_expression_le_card_primesInQuarterInterval hX
  rw [div_le_iff₀ hlogX] at hexplicit
  calc
    log 2 / 4 * X
        ≤ ((X : ℝ) * log 2 - log (X + 1) -
              2 * √(X : ℝ) * log X) -
            log 4 * (X / 4 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one] at herror
      ring_nf at herror hquarter ⊢
      linarith
    _ ≤ (#(primesInQuarterInterval X) : ℝ) * log X :=
      hexplicit
