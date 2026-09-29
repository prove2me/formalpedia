-- Prove2me | solution 1 for mme_laser_block_dimension_count_refined
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-01T02:07:15.739765+00:00
-- url     : https://prove2.me/submissions/dda6785e-7b9a-458d-8c4c-1a35d50040b2

import Definitions.Def_mme_laser_pattern
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

open BigOperators Filter

universe u

/-! ## Helper lemmas (top-level, fresh context)

Prove2Me's server build can reject `linarith`/`nlinarith` calls that succeed
locally when many `set`-bound real definitions and universal-quantifier
hypotheses are in scope. We extract each such call into a top-level private
helper with a minimal explicit context. -/

namespace MMELaserBlockDimRefinedHelpers

/-- The single-summand bound from `log y ≤ y - 1`:
for `p ≥ 0`, `Real.log 0 = 0`, and `Real.log` Mathlib-convention,
`-p * Real.log p ≤ p * Real.log C + (1/C - p)` when `0 < C`.

Proof: case `p = 0` gives `0 ≤ 1/C`. Case `p > 0`: apply
`log_le_sub_one_of_pos` to `1/(C·p)`, rearrange. -/
private lemma single_term_bound {C p : ℝ}
    (hC_pos : 0 < C) (hp : 0 ≤ p) :
    -(p * Real.log p) ≤ p * Real.log C + (1 / C - p) := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · -- p = 0
    have hp0' : p = 0 := hp0.symm
    rw [hp0']
    -- Goal: -(0 * log 0) ≤ 0 * log C + (1/C - 0).
    have h_lhs : -((0 : ℝ) * Real.log 0) = 0 := by ring
    have h_rhs : (0 : ℝ) * Real.log C + (1 / C - 0) = 1 / C := by ring
    rw [h_lhs, h_rhs]
    exact (one_div_pos.mpr hC_pos).le
  · -- p > 0
    set y : ℝ := 1 / (C * p)
    have hCp : 0 < C * p := mul_pos hC_pos hp0
    have hy_pos : 0 < y := by
      show 0 < 1 / (C * p)
      exact one_div_pos.mpr hCp
    have hlog : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy_pos
    -- log y = log (1 / (C * p)) = -log (C * p) = -(log C + log p)
    have hlog_y_eq : Real.log y = -(Real.log C + Real.log p) := by
      show Real.log (1 / (C * p)) = -(Real.log C + Real.log p)
      rw [Real.log_div one_ne_zero (ne_of_gt hCp), Real.log_one, zero_sub,
          Real.log_mul (ne_of_gt hC_pos) (ne_of_gt hp0)]
    have hy_eq : y = 1 / (C * p) := rfl
    -- log_le_sub_one says log y ≤ 1/(C·p) - 1
    rw [hlog_y_eq, hy_eq] at hlog
    -- so: -(log C + log p) ≤ 1/(C*p) - 1
    -- multiply by p > 0:
    have hmul : p * (-(Real.log C + Real.log p)) ≤ p * (1 / (C * p) - 1) :=
      mul_le_mul_of_nonneg_left hlog hp0.le
    -- LHS = -p * log C - p * log p
    -- RHS = p / (C*p) - p = 1/C - p
    have hRHS : p * (1 / (C * p) - 1) = 1 / C - p := by
      have hCne : C ≠ 0 := ne_of_gt hC_pos
      have hpne : p ≠ 0 := ne_of_gt hp0
      field_simp
    rw [hRHS] at hmul
    -- Now: p * (-(log C + log p)) ≤ 1/C - p
    -- Rearrange: -(p · log p) ≤ p · log C + (1/C - p)
    nlinarith [hmul]

/-- Two ε-positivity helpers (server-stable). -/
private lemma neg_log2_eps_le_zero {Lt eps : ℝ}
    (hL_pos : 0 < Lt) (heps : 0 < eps) :
    Lt * (-eps) ≤ 0 := by
  have : 0 < Lt * eps := mul_pos hL_pos heps
  linarith

private lemma mul_nonneg_N {a : ℝ} (N : ℕ) (ha : a ≤ 0) : a * (N : ℝ) ≤ 0 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact mul_nonpos_of_nonpos_of_nonneg ha hN

/-- For any real `a, b, c, N` with `a ≤ b` and `0 ≤ N`,
`a * N ≤ b * N`. (Local helper kept context-light.) -/
private lemma mul_le_mul_right_N {a b : ℝ} (N : ℕ) (hab : a ≤ b) :
    a * (N : ℝ) ≤ b * (N : ℝ) :=
  mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N)

/-- `a + b ≤ c` from `a ≤ c` and `b ≤ 0`. -/
private lemma combine_neg_helper {a b c : ℝ}
    (ha : a ≤ c) (hb : b ≤ 0) :
    a + b ≤ c := by linarith

/-- `x * y = 1` (when `x ≠ 0`, with `y = 1/x`) ⇒ `x * y - 1 = 0`. -/
private lemma card_inv_helper {C : ℝ} (hC : C ≠ 0) :
    C * (1 / C) - 1 = 0 := by
  have h1 : C * (1 / C) = 1 := by field_simp
  rw [h1]; ring

end MMELaserBlockDimRefinedHelpers

open MMELaserBlockDimRefinedHelpers

/-- **Stirling/multinomial lower bound on the count of type-distributed multi-types.**

For a cyclically-symmetric support pattern `S ⊆ (Fin t)^3` and a probability
distribution `p` on `S` whose three coordinate-marginals are equal, the number of
length-`N` sequences in `S^N` whose empirical type-distribution is approximately
`p` is bounded below asymptotically by `≥ exp(N · log 2 · (H(p) - ε))` for every
`ε > 0`, where `H(p) = -∑ p_x · log_2 p_x` is the Shannon entropy of `p` in bits.

**Easy-witness proof.** Pick `k = S.card ^ N`. The upper bound `k ≤ S.card ^ N`
is then trivial. The lower bound reduces (via `Real.log`) to the entropy bound
`H(p) ≤ log_2 S.card`, which we prove from the elementary `log y ≤ y - 1`
inequality (Gibbs-style termwise: apply to `y = 1/(S.card · p_x)` and sum).
The `Frequently` quantifier is discharged with `Frequently.of_forall` since the
witness construction works for every `N : ℕ`. -/
theorem solution
    {t : ℕ} (S : Finset (Fin t × Fin t × Fin t))
    (_hSym : MME.LaserSymmetric S)
    (p : (Fin t × Fin t × Fin t) → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (_hp_zero_off : ∀ x ∉ S, p x = 0)
    (hp_sum : ∑ x ∈ S, p x = 1)
    (_hp_cyclic_12 : ∀ α : Fin t,
      ∑ x ∈ S, (if x.1 = α then p x else 0) =
      ∑ x ∈ S, (if x.2.1 = α then p x else 0))
    (_hp_cyclic_23 : ∀ α : Fin t,
      ∑ x ∈ S, (if x.2.1 = α then p x else 0) =
      ∑ x ∈ S, (if x.2.2 = α then p x else 0)) :
    ∀ ε > (0 : ℝ), ∃ᶠ N : ℕ in atTop,
      ∃ k : ℕ,
        Real.exp ((Real.log 2) *
          (((∑ x ∈ S, (-p x) * (Real.log (p x) / Real.log 2)) - ε) * (N : ℝ))) ≤ (k : ℝ)
        ∧ (k : ℕ) ≤ S.card ^ N := by
  intro ε hε
  -- Step 1: S is nonempty (from hp_sum = 1 ≠ 0 = ∑ x ∈ ∅, _).
  have hS_nonempty : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hp_sum
    exact (by norm_num : (0 : ℝ) ≠ 1) hp_sum
  have hScard_pos : 0 < S.card := Finset.card_pos.mpr hS_nonempty
  have hScard_pos_R : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hScard_pos
  have hScard_ne_R : (S.card : ℝ) ≠ 0 := ne_of_gt hScard_pos_R
  -- Step 2: abbreviations.
  set L : ℝ := Real.log 2 with hL_def
  have hL_pos : 0 < L := Real.log_pos (by norm_num)
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  set Hbits : ℝ := ∑ x ∈ S, (-p x) * (Real.log (p x) / Real.log 2) with hHbits_def
  -- Step 3: prove `L * Hbits ≤ Real.log S.card`.
  -- L * Hbits = ∑ x ∈ S, -(p x * Real.log (p x)).
  have hLHbits :
      L * Hbits = ∑ x ∈ S, -(p x * Real.log (p x)) := by
    rw [hHbits_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    -- L * ((-p x) * (Real.log (p x) / L)) = -(p x * Real.log (p x))
    show L * ((-p x) * (Real.log (p x) / L)) = -(p x * Real.log (p x))
    field_simp
  -- Termwise entropy bound: -(p x · log p x) ≤ p x · log S.card + (1/S.card - p x).
  have hterm : ∀ x ∈ S,
      -(p x * Real.log (p x)) ≤
        p x * Real.log (S.card : ℝ) + (1 / (S.card : ℝ) - p x) := by
    intro x _
    exact single_term_bound hScard_pos_R (hp_nonneg x)
  -- Sum the termwise bound.
  have hSum_bound :
      ∑ x ∈ S, -(p x * Real.log (p x)) ≤
        ∑ x ∈ S, (p x * Real.log (S.card : ℝ) + (1 / (S.card : ℝ) - p x)) :=
    Finset.sum_le_sum hterm
  -- Compute the RHS = log S.card · 1 + (S.card · (1/S.card) - 1) = log S.card.
  have hRHS_eq :
      ∑ x ∈ S, (p x * Real.log (S.card : ℝ) + (1 / (S.card : ℝ) - p x)) =
        Real.log (S.card : ℝ) := by
    rw [Finset.sum_add_distrib]
    -- ∑ p x · log S.card = log S.card · ∑ p x = log S.card · 1.
    have h1 : ∑ x ∈ S, p x * Real.log (S.card : ℝ) = Real.log (S.card : ℝ) := by
      rw [← Finset.sum_mul, hp_sum, one_mul]
    -- ∑ (1/S.card - p x) = S.card · (1/S.card) - 1 = 0.
    have h2 : ∑ x ∈ S, ((1 / (S.card : ℝ)) - p x) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hp_sum]
      -- Goal: S.card • (1/(S.card:ℝ)) - 1 = 0
      rw [nsmul_eq_mul]
      exact card_inv_helper hScard_ne_R
    rw [h1, h2, add_zero]
  -- Combine.
  have hL_Hbits_le : L * Hbits ≤ Real.log (S.card : ℝ) := by
    rw [hLHbits]
    rw [← hRHS_eq]
    exact hSum_bound
  -- Step 4: apply `Frequently.of_forall` — prove the statement for every N.
  apply Frequently.of_forall
  intro N
  refine ⟨S.card ^ N, ?_, le_refl _⟩
  -- Goal: exp (L * ((Hbits - ε) * N)) ≤ (S.card ^ N : ℕ) cast to ℝ
  -- = (S.card : ℝ) ^ N.
  have hcast : ((S.card ^ N : ℕ) : ℝ) = (S.card : ℝ) ^ N := by push_cast; ring
  rw [hcast]
  -- Now: exp (L * ((Hbits - ε) * N)) ≤ (S.card : ℝ) ^ N.
  -- Rewrite (S.card : ℝ) ^ N = exp (N * log S.card).
  have hScard_pow_eq :
      (S.card : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log (S.card : ℝ)) := by
    rw [Real.exp_nat_mul]
    rw [Real.exp_log hScard_pos_R]
  rw [hScard_pow_eq]
  apply Real.exp_le_exp.mpr
  -- Goal: L * ((Hbits - ε) * N) ≤ N * log S.card.
  -- We have L * Hbits ≤ log S.card and L * (-ε) ≤ 0, so
  -- L * (Hbits - ε) ≤ L * Hbits ≤ log S.card. Multiply by N ≥ 0.
  have h_eps_neg : L * (-ε) ≤ 0 := neg_log2_eps_le_zero hL_pos hε
  have h_combined : L * (Hbits - ε) ≤ Real.log (S.card : ℝ) := by
    have heq : L * (Hbits - ε) = L * Hbits + L * (-ε) := by ring
    have hbound : L * Hbits + L * (-ε) ≤ Real.log (S.card : ℝ) :=
      combine_neg_helper hL_Hbits_le h_eps_neg
    rw [heq]
    exact hbound
  -- Multiply by N ≥ 0:
  have h_mul_N : L * (Hbits - ε) * (N : ℝ) ≤ Real.log (S.card : ℝ) * (N : ℝ) :=
    mul_le_mul_right_N N h_combined
  -- Rearrange both sides.
  have h_lhs_eq : L * ((Hbits - ε) * (N : ℝ)) = L * (Hbits - ε) * (N : ℝ) := by ring
  have h_rhs_eq : Real.log (S.card : ℝ) * (N : ℝ) =
                  (N : ℝ) * Real.log (S.card : ℝ) := by ring
  rw [h_lhs_eq, ← h_rhs_eq]
  exact h_mul_N
