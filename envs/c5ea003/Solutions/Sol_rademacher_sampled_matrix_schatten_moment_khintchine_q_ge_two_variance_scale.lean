-- Prove2me | solution 1 for rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T20:39:25.923772+00:00
-- url     : https://prove2.me/submissions/a89cdcd4-0c2e-4433-9745-34ca4564f30c

import Definitions.Def_matrix_completion_gram_schatten
import Theorems.Thm_rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2
import Theorems.Thm_gram_schatten_le_exp_half_variance_scale
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MatrixCompletion

/-
Reduction of `rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale`
(3090c7ef, the source-faithful q≥2 Khintchine-to-variance branch of d6e02cfd) to
  * Core A q2 `rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2`
    (155bda95) — the noncommutative (Lust-Picquard/Buchholz) Khintchine inequality for the
    sampled coordinate Rademacher series with the diagonal-Gram Schatten RHS
    `C·√q·max(rowGramSchatten,colGramSchatten)` for `2 ≤ q` (CR2009 §6.1 Lemma 6.1 p.24;
    Buchholz Math. Ann. 319 (2001) 1-16, even-integer trace-moment method), and
  * Node B `gram_schatten_le_exp_half_variance_scale` (6090ab2e, Proved) — the `ℓ_q→ℓ_∞`
    comparison + window collapse `max(rowGram,colGram) ≤ e^{1/2}·varScale` for `q ≥ β log(max n)`,
    `β>2` (CR2009 §6.1, `‖·‖ ≤ ‖·‖_{S_q} ≤ e‖·‖` bridge p.24).

The target is the monotone `∀ C', Ckh ≤ C' → …` form: Core A gives the moment ≤ `(C·√q·maxGram)^q`,
Node B gives `maxGram ≤ e^{1/2}·V`, so the moment ≤ `(C·e^{1/2}·√q·V)^q ≤ (C'·√q·V)^q` for any
`C' ≥ Ckh := C·e^{1/2}` by `pow_le_pow_left₀` (nonneg base).
-/

theorem solution :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ C' : ℝ, Ckh ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C' * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  obtain ⟨C, hCpos, hCore⟩ :=
    rademacher_sampled_matrix_noncommutative_khintchine_diagonal_gram_bound_q2
  refine ⟨C * Real.exp (1 / 2), by positivity, ?_⟩
  intro C' hC' β hβ n₁ n₂ m q Omega X hq hqlog
  have hppos : (0 : ℝ) ≤ (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  -- need 1 ≤ q for Node B; follows from 2 ≤ q
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  -- Core A q2: moment ≤ (C·√q·max Gram)^q
  have hA := hCore β hβ n₁ n₂ m q Omega X hq hqlog
  -- Node B: max Gram ≤ e^{1/2}·V
  have hB :=
    gram_schatten_le_exp_half_variance_scale Omega
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ) β hppos hβ hqR hqlog
  set V := rademacherSampledVarianceScale Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X with hV
  set G := max (sampledRowGramSchatten Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
               (sampledColumnGramSchatten Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
    with hG
  have hVnn : 0 ≤ V := by
    rw [hV]; unfold rademacherSampledVarianceScale; positivity
  have hGnn : 0 ≤ G := by
    rw [hG]
    apply le_max_of_le_left
    unfold sampledRowGramSchatten
    exact Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (by positivity) _)) _
  -- (C·√q·G)^q ≤ (C·√q·(e^{1/2}·V))^q  [Node B]
  have hbase_nn : 0 ≤ C * Real.sqrt (q : ℝ) * G := by positivity
  have hbase_le : C * Real.sqrt (q : ℝ) * G ≤ C * Real.sqrt (q : ℝ) * (Real.exp (1/2) * V) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hpow_le :
      (C * Real.sqrt (q : ℝ) * G) ^ q ≤
        (C * Real.sqrt (q : ℝ) * (Real.exp (1/2) * V)) ^ q :=
    pow_le_pow_left₀ hbase_nn hbase_le q
  -- rewrite to Ckh = C·e^{1/2}
  have hring :
      (C * Real.sqrt (q : ℝ) * (Real.exp (1/2) * V)) ^ q =
        (C * Real.exp (1 / 2) * Real.sqrt (q : ℝ) * V) ^ q := by
    congr 1; ring
  -- monotone in C': Ckh = C·e^{1/2} ≤ C'
  have hCkh_nn : 0 ≤ C * Real.exp (1 / 2) := by positivity
  have hsqrt_nn : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hmono :
      (C * Real.exp (1 / 2) * Real.sqrt (q : ℝ) * V) ^ q ≤
        (C' * Real.sqrt (q : ℝ) * V) ^ q := by
    apply pow_le_pow_left₀ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hVnn
    exact mul_le_mul_of_nonneg_right hC' hsqrt_nn
  exact le_trans hA (le_trans hpow_le (le_trans (le_of_eq hring) hmono))
