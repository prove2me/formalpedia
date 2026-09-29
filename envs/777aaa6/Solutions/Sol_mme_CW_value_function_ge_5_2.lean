-- Prove2me | solution 1 for mme_CW_value_function_ge_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-01T01:09:30.687786+00:00
-- url     : https://prove2.me/submissions/9cee1560-ade8-4838-ab0a-1aabfc2152d5

import Definitions.Def_mme_CW_value_function
import Mathlib.Analysis.Complex.ExponentialBounds

/-! ## Helper lemmas (top-level, fresh context)

Prove2Me's server build occasionally rejects `linarith`/`nlinarith` calls
that succeed locally when many `set`-bound real definitions and universal-
quantifier hypotheses sit in scope. We sidestep that by extracting every
such call into a top-level private helper that takes ONLY the explicit
inequalities it needs. Each helper has a fresh, minimal context. -/

namespace MMECWValueHelpers

/-- For `L ≠ 0`, `1/L + 1/L + 1/L = 3/L`. (Used to flatten the entropy sum.) -/
private lemma three_inv_sum {L : ℝ} (hL_ne : L ≠ 0) :
    (1 / L) + (1 / L) + (1 / L) = 3 / L := by
  field_simp; ring

/-- Sum of three entropy-term upper bounds. -/
private lemma sum_entropy_helper {L Sa Sb Sc : ℝ}
    (hL_ne : L ≠ 0)
    (hHa : Sa ≤ 1 / L)
    (hHb : Sb ≤ 1 / L)
    (hHc : Sc ≤ 1 / L) :
    Sa + Sb + Sc ≤ 3 / L := by
  have h3 : (1 / L) + (1 / L) + (1 / L) = 3 / L := by field_simp; ring
  linarith [hHa, hHb, hHc, h3]

/-- `4 * log 3 - L = log (81/2)` given `log 81 = 4 * log 3` and
    `log (81/2) = log 81 - L`. -/
private lemma log_81_2_helper {L a b : ℝ}
    (h81 : a = 4 * Real.log 3)
    (h812 : b = a - L) :
    4 * Real.log 3 - L = b := by
  linarith [h81, h812]

/-- Final bound for the `5/2 ≤ V` step: given the three rewriting facts
    and monotonicity of `log`, conclude `log (5/2) ≤ (4/3) log 3 - L/3`. -/
private lemma log_52_helper {L A C D : ℝ}
    (h_log_125_8 : 3 * A = C)
    (h_log_81_2 : 4 * Real.log 3 - L = D)
    (h_log_mono : C ≤ D) :
    A ≤ (4/3) * Real.log 3 - L/3 := by
  linarith [h_log_125_8, h_log_81_2, h_log_mono]

/-- `log 6 ≤ 3 * L` from `log 6 ≤ log 8` and `log 8 = 3 * L`. -/
private lemma log_6_le_helper {L A B : ℝ}
    (h6le8 : A ≤ B)
    (h8 : B = 3 * L) :
    A ≤ 3 * L := by
  linarith [h6le8, h8]

/-- The last step: bound `(α/3) * (L6 / L) ≤ 1`, given `0 ≤ L6 ≤ 3 L`. -/
private lemma last_term_helper {α L L6 : ℝ}
    (hL_pos : 0 < L)
    (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1)
    (hL6_nn : 0 ≤ L6)
    (h6 : L6 ≤ 3 * L) :
    (α / 3) * (L6 / L) ≤ 1 := by
  have hαL : α / 3 ≤ 1 / 3 := by linarith
  have hL6divL_nn : 0 ≤ L6 / L := div_nonneg hL6_nn hL_pos.le
  have step1 : (α / 3) * (L6 / L) ≤ (1 / 3) * (L6 / L) :=
    mul_le_mul_of_nonneg_right hαL hL6divL_nn
  have hL6_le : L6 / L ≤ 3 := by
    rw [div_le_iff₀ hL_pos]; linarith [h6]
  have step2 : (1 / 3 : ℝ) * (L6 / L) ≤ (1 / 3) * 3 :=
    mul_le_mul_of_nonneg_left hL6_le (by norm_num)
  have step3 : (1 / 3 : ℝ) * 3 = 1 := by norm_num
  linarith [step1, step2, step3]

/-- `3 / L ≤ 6` from `1/2 < L`. -/
private lemma three_div_L_le_six_helper {L : ℝ}
    (hL_pos : 0 < L)
    (hL_gt : (1 : ℝ) / 2 < L) :
    3 / L ≤ 6 := by
  rw [div_le_iff₀ hL_pos]
  -- Goal: 3 ≤ 6 * L. From hL_gt: 1/2 < L, so 6 * L > 6 * (1/2) = 3.
  have h6L : 6 * ((1 : ℝ) / 2) < 6 * L :=
    mul_lt_mul_of_pos_left hL_gt (by norm_num)
  have hcalc : 6 * ((1 : ℝ) / 2) = 3 := by norm_num
  linarith [h6L, hcalc]

/-- Final assembly: `H + last ≤ 3/L + 1 ≤ 6 + 4 ≤ 10`. -/
private lemma final_assembly_helper {Esum Eα t3 : ℝ}
    (h_sum_entropy : Esum ≤ t3)
    (h_last : Eα ≤ 1)
    (h3L : t3 ≤ 6) :
    Esum + Eα ≤ 10 := by
  linarith [h_sum_entropy, h_last, h3L]

/-- `−(x · log x) ≤ 1` for `x ∈ [0, 1]`. Local helper kept inline-free of
    inherited context for safety. -/
private lemma neg_log_mul_le_helper (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    -(x * Real.log x) ≤ 1 := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · subst hx0; simp
  · have hbd : |Real.log x * x| < 1 := Real.abs_log_mul_self_lt x hx0 hx1
    have habs := abs_le.mp hbd.le
    have hcomm : Real.log x * x = x * Real.log x := by ring
    rw [hcomm] at habs
    linarith [habs.1]

/-- `(-p) * (log p / L) ≤ 1/L` for `p ∈ [0,1]`, `L > 0`. -/
private lemma entropy_term_bd_helper {L : ℝ} (hL_pos : 0 < L)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (-p) * (Real.log p / L) ≤ 1 / L := by
  have h1 : (-p) * (Real.log p / L) = -(p * Real.log p) / L := by field_simp
  rw [h1]
  have hbase : -(p * Real.log p) ≤ 1 := neg_log_mul_le_helper p hp hp1
  exact (div_le_div_of_nonneg_right hbase hL_pos.le).trans (by rfl)

/-- Triangle bounds: `0 ≤ (2 - α)/3 ≤ 1` for `0 ≤ α ≤ 1`. -/
private lemma triangle_a {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ (2 - α) / 3 ∧ (2 - α) / 3 ≤ 1 := by
  refine ⟨?_, ?_⟩ <;> [linarith; linarith]

private lemma triangle_b {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ 2 * α / 3 ∧ 2 * α / 3 ≤ 1 := by
  refine ⟨?_, ?_⟩ <;> [linarith; linarith]

private lemma triangle_c {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ (1 - α) / 3 ∧ (1 - α) / 3 ≤ 1 := by
  refine ⟨?_, ?_⟩ <;> [linarith; linarith]

end MMECWValueHelpers

open MMECWValueHelpers

/-- **The CW laser-method value at q = 6 is at least 5/2.**

This is the concrete numeric witness that lets the laser-method chain conclude
`ω < 2.376` for Coppersmith–Winograd's tensor: the closed-form value
`cwValueFunction 6` (from Filmus Theorem 2.5 / CW 1990 §6) exceeds the
threshold `5/2` required by the L1-α-poly bridge.

**Proof strategy:** Use the witness `α = 1` (all probability mass on the
three "middle" type-triples of the CW support pattern). The formula
evaluates to

  `2^{(4/3) log₂ 3 - 1/3}`,

and the inequality `5/2 ≤ 2^{(4/3) log₂ 3 - 1/3}` reduces (after taking
log₂, multiplying by 3, and exponentiating) to `125/4 ≤ 81`, which is
trivially true by `norm_num`.

(The actual optimum of `cwValueFunction 6` is at `α ≈ 0.725` with
value ≈ 3.92; the `α = 1` witness gives ≈ 3.43, well above 5/2.)

**Reusability.** The cleanest path to "ω-bound bridges that need a value ≥ V"
in any laser-method paper. The witness pattern (pick an interior α, compute
the entropy + log_q expression, reduce to elementary arithmetic) generalises
to any q and any value threshold; Stothers, Vassilevska Williams, Le Gall
all instantiate the same logic at their own optimization parameters. -/
theorem solution : (5 : ℝ) / 2 ≤ MME.cwValueFunction 6 := by
  -- Abbreviation: `L = log 2 > 0`.
  set L : ℝ := Real.log 2 with hL_def
  have hL_pos : 0 < L := Real.log_pos (by norm_num)
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  -- Common log identities used in both subproofs.
  have hlog13 : Real.log ((1:ℝ)/3) = -Real.log 3 := by
    rw [Real.log_div one_ne_zero (by norm_num), Real.log_one]; ring
  have hlog23 : Real.log ((2:ℝ)/3) = Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have hlog6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    have h63 : (6 : ℝ) = 2 * 3 := by norm_num
    rw [h63, Real.log_mul (by norm_num) (by norm_num)]
  -- The formula value at α = 1.
  set V : ℝ :=
    Real.exp (Real.log 2 *
      (MME.H3 ((2 - 1) / 3) (2 * 1 / 3) ((1 - 1) / 3)
        + (1 / 3) * ((fun x => Real.log x / Real.log 2) ((6 : ℕ) : ℝ))))
    with hV_def
  -- Step A: V is in the defining set.
  have hV_mem : V ∈ { v : ℝ | ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
      v = Real.exp (Real.log 2 *
        (MME.H3 ((2 - α) / 3) (2 * α / 3) ((1 - α) / 3)
          + (α / 3) * (fun x => Real.log x / Real.log 2) ((6 : ℕ) : ℝ))) } := by
    refine ⟨(1 : ℝ), by norm_num, by norm_num, ?_⟩
    rfl
  -- Step B: 5/2 ≤ V.
  have hV_ge : (5 : ℝ) / 2 ≤ V := by
    -- Simplify the exponent: L * (H3(1/3, 2/3, 0) + (1/3) log_2 6) = (4/3) log 3 - L/3.
    have hExpArg :
        Real.log 2 * (MME.H3 ((2 - 1) / 3) (2 * 1 / 3) ((1 - 1) / 3)
            + (1 / 3) * ((fun x => Real.log x / Real.log 2) ((6 : ℕ) : ℝ)))
        = (4/3) * Real.log 3 - L/3 := by
      have hcast : ((6 : ℕ) : ℝ) = (6 : ℝ) := by norm_num
      have h1 : (2 - (1:ℝ)) / 3 = 1/3 := by norm_num
      have h2 : 2 * (1:ℝ) / 3 = 2/3 := by norm_num
      have h3 : (1 - (1:ℝ)) / 3 = 0 := by norm_num
      simp only [MME.H3, h1, h2, h3, hcast]
      rw [hlog13, hlog23, hlog6, Real.log_zero]
      field_simp
      ring
    have hV_eq : V = Real.exp ((4/3) * Real.log 3 - L/3) := by
      rw [hV_def, hExpArg]
    rw [hV_eq]
    -- Now: 5/2 ≤ Real.exp ((4/3) * log 3 - L/3)
    -- Equivalent to log(5/2) ≤ (4/3) log 3 - L/3.
    rw [← Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 5/2)]
    -- Multiply by 3: 3 log(5/2) ≤ 4 log 3 - L, i.e. log(125/8) ≤ log(81/2).
    have h_log_125_8 : 3 * Real.log ((5:ℝ)/2) = Real.log (125/8) := by
      have hpow : ((5:ℝ)/2)^3 = 125/8 := by norm_num
      have hlpow := Real.log_pow ((5:ℝ)/2) 3
      rw [← hpow, hlpow]; push_cast; ring
    have hlog81 : Real.log (81 : ℝ) = 4 * Real.log 3 := by
      have h81 : (81 : ℝ) = 3^4 := by norm_num
      rw [h81, Real.log_pow]; push_cast; ring
    have hlog81_2 : Real.log ((81:ℝ)/2) = Real.log 81 - L := by
      rw [Real.log_div (by norm_num) (by norm_num)]
    have h_log_81_2 : 4 * Real.log 3 - L = Real.log (81/2) :=
      log_81_2_helper hlog81 hlog81_2
    have h_num : (125 : ℝ) / 8 ≤ 81 / 2 := by norm_num
    have h_pos1 : (0 : ℝ) < 125 / 8 := by norm_num
    have h_log_mono : Real.log (125/8) ≤ Real.log (81/2) :=
      Real.log_le_log h_pos1 h_num
    exact log_52_helper h_log_125_8 h_log_81_2 h_log_mono
  -- Step C: assemble via `le_csSup_of_le`.
  apply le_csSup_of_le _ hV_mem hV_ge
  -- BddAbove. Crude bound: `Real.exp (L * 10)`.
  refine ⟨Real.exp (L * 10), ?_⟩
  rintro v ⟨α, hα0, hα1, rfl⟩
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hL_pos)
  -- a, b, c are the three probabilities at α; each in [0,1].
  set a : ℝ := (2 - α) / 3 with ha_def
  set b : ℝ := 2 * α / 3 with hb_def
  set c : ℝ := (1 - α) / 3 with hc_def
  have ⟨ha0, ha1⟩ := triangle_a hα0 hα1
  have ⟨hb0, hb1⟩ := triangle_b hα0 hα1
  have ⟨hc0, hc1⟩ := triangle_c hα0 hα1
  have hHa := entropy_term_bd_helper hL_pos a ha0 ha1
  have hHb := entropy_term_bd_helper hL_pos b hb0 hb1
  have hHc := entropy_term_bd_helper hL_pos c hc0 hc1
  -- Bound (α/3) * log 6 / L ≤ 1.
  have h6 : Real.log 6 ≤ 3 * L := by
    have h6le8 : Real.log 6 ≤ Real.log 8 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have h8 : Real.log 8 = 3 * L := by
      have h82 : (8 : ℝ) = 2^3 := by norm_num
      rw [h82, Real.log_pow]; push_cast; ring
    exact log_6_le_helper h6le8 h8
  have hlog6_nn : 0 ≤ Real.log 6 :=
    Real.log_nonneg (by norm_num)
  have h_last : (α/3) * (Real.log 6 / L) ≤ 1 :=
    last_term_helper hL_pos hα0 hα1 hlog6_nn h6
  -- Bound 3/L ≤ 6 using L > 1/2. Avoid `linarith` on real decimals (server-side
  -- linarith struggles with `(0.6931471803 : ℝ) > 1/2`); use explicit `calc` + `lt_trans`.
  have hL_gt : (1 : ℝ) / 2 < L := by
    show (1 : ℝ) / 2 < Real.log 2
    calc (1 : ℝ) / 2 < 0.6931471803 := by norm_num
      _ < Real.log 2 := Real.log_two_gt_d9
  have h3L : 3 / L ≤ 6 := three_div_L_le_six_helper hL_pos hL_gt
  -- Now assemble: H3 + (α/3) * log 6 / L ≤ 3/L + 1 ≤ 5 + 1 = 6 ≤ 10.
  unfold MME.H3
  have hcast : ((6 : ℕ) : ℝ) = (6 : ℝ) := by norm_num
  show (-a) * (Real.log a / L) + (-b) * (Real.log b / L)
      + (-c) * (Real.log c / L)
      + (α/3) * (Real.log (((6 : ℕ) : ℝ)) / L) ≤ 10
  rw [hcast]
  have h_sum_entropy : (-a) * (Real.log a / L) + (-b) * (Real.log b / L)
      + (-c) * (Real.log c / L) ≤ 3 / L :=
    sum_entropy_helper hL_ne hHa hHb hHc
  -- Now: h_sum_entropy + h_last ≤ 3/L + 1 ≤ 7 ≤ 10.
  exact final_assembly_helper h_sum_entropy h_last h3L
