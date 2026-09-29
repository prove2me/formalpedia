-- Prove2me | solution 1 for rademacher_sampled_matrix_noncommutative_khintchine_q2_from_even_trace_pairbound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-23T22:20:58.507725+00:00
-- url     : https://prove2.me/submissions/c407b5bc-b619-467d-b6f9-f9275dd75192

import Theorems.Thm_rademacher_expectation_power_mean
import Theorems.Thm_rank_rpow_inv_le_exp_one_of_log_le
import Theorems.Thm_buchholz_double_factorial_constant_bound
import Theorems.Thm_sampled_row_gram_schatten_antitone_exp
import Theorems.Thm_sampled_column_gram_schatten_antitone_exp
import Theorems.Thm_spectral_norm_le_schatten_norm
import Theorems.Thm_schatten_norm_le_rank_rpow_smul_spectral_norm
import Theorems.Thm_rademacher_expectation_monotone

open scoped Classical BigOperators
open Matrix MatrixCompletion

-- ============ SUPPORT LEMMAS ============

/-- Schatten norm is nonneg (rpow of a nonneg sum). -/
lemma bridge_schattenNorm_nonneg {n1 n2 : Nat} (q : ℝ) (X : RealMatrix n1 n2) :
    0 ≤ schattenNorm q X := by
  unfold schattenNorm
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg
  intro k _
  exact Real.rpow_nonneg (LinearMap.singularValues_nonneg _ _) _

/-- MatrixCompletion.spectralNorm nonneg. -/
lemma bridge_spectralNorm_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ MatrixCompletion.spectralNorm X := by
  unfold MatrixCompletion.spectralNorm
  exact norm_nonneg _

/-- sampledRowGramSchatten nonneg (p ≥ 0). -/
lemma bridge_rowGS_nonneg {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 ≤ p)
    (X : RealMatrix n1 n2) (q : ℝ) : 0 ≤ sampledRowGramSchatten Omega p X q := by
  unfold sampledRowGramSchatten
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg; intro i _
  apply Real.rpow_nonneg
  apply mul_nonneg (inv_nonneg.mpr hp)
  exact Real.sqrt_nonneg _

/-- sampledColumnGramSchatten nonneg (p ≥ 0). -/
lemma bridge_colGS_nonneg {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 ≤ p)
    (X : RealMatrix n1 n2) (q : ℝ) : 0 ≤ sampledColumnGramSchatten Omega p X q := by
  unfold sampledColumnGramSchatten
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg; intro j _
  apply Real.rpow_nonneg
  apply mul_nonneg (inv_nonneg.mpr hp)
  exact Real.sqrt_nonneg _

/-- Schatten norm of the zero matrix is zero (for q ≠ 0). -/
lemma bridge_schattenNorm_zero {n1 n2 : Nat} (q : ℝ) (hq : q ≠ 0) :
    schattenNorm q (0 : RealMatrix n1 n2) = 0 := by
  unfold schattenNorm
  rw [show (Matrix.toEuclideanLin (0 : RealMatrix n1 n2)) = 0 by simp]
  rw [LinearMap.singularValues_zero]
  have key : ∀ s : ℝ, s = 0 → Real.rpow s q⁻¹ = 0 :=
    fun s hs => by rw [hs]; exact Real.zero_rpow (inv_ne_zero hq)
  apply key
  apply Finset.sum_eq_zero
  intro k _
  show Real.rpow (0:ℝ) q = 0
  exact Real.zero_rpow hq

/-- Pointwise op-norm sandwich: `schattenNorm q S ≤ e · schattenNorm (2n) S`.
Combines F6 (schatten ≤ rank^{1/q}·spectral) + window (rank^{1/q} ≤ e) + F5
(spectral ≤ schatten 2n). Handles rank = 0. -/
lemma bridge_pointwise_sandwich {n1 n2 : Nat} (S : RealMatrix n1 n2)
    (q : ℝ) (hq : 1 ≤ q) (nn : ℕ) (hnn : 1 ≤ nn)
    (hqle : q ≤ (2 * nn : ℝ))
    (hlogR : Real.log
        ((Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin S)) : ℝ)) ≤ q) :
    schattenNorm q S ≤ Real.exp 1 * schattenNorm (2 * nn : ℝ) S := by
  set R : ℕ := Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin S)) with hRdef
  have hF6 : schattenNorm q S ≤ Real.rpow (R : ℝ) q⁻¹ * MatrixCompletion.spectralNorm S := schatten_norm_le_rank_rpow_smul_spectral_norm q S hq
  -- F5 at exponent (2*nn : ℕ)
  have hF5 := spectral_norm_le_schatten_norm (2 * nn) S (by omega)
  have hcast : ((2 * nn : ℕ) : ℝ) = (2 * nn : ℝ) := by push_cast; ring
  rw [hcast] at hF5
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · -- R = 0 ⇒ R^{1/q} = 0 ⇒ schatten q S ≤ 0 ≤ e·schatten 2n
    have : schattenNorm q S ≤ 0 := by
      refine le_trans hF6 ?_
      rw [hR0, Nat.cast_zero]
      rw [show Real.rpow 0 q⁻¹ = (0:ℝ) from Real.zero_rpow (by positivity)]
      simp
    refine le_trans this ?_
    have := bridge_schattenNorm_nonneg (2 * nn : ℝ) S
    positivity
  · -- R ≥ 1
    have hR1 : 1 ≤ R := hRpos
    have hwin := rank_rpow_inv_le_exp_one_of_log_le R q hR1 hq hlogR
    -- schatten q S ≤ R^{1/q}·spectral S ≤ e·spectral S ≤ e·schatten 2n S
    calc schattenNorm q S
        ≤ Real.rpow (R : ℝ) q⁻¹ * MatrixCompletion.spectralNorm S := hF6
      _ ≤ Real.exp 1 * MatrixCompletion.spectralNorm S := by
            apply mul_le_mul_of_nonneg_right hwin (bridge_spectralNorm_nonneg S)
      _ ≤ Real.exp 1 * schattenNorm (2 * nn : ℝ) S := by
            apply mul_le_mul_of_nonneg_left hF5 (le_of_lt (Real.exp_pos 1))

/-- rademacherExpectation pulls out a nonneg constant factor. -/
lemma bridge_rademacherExpectation_const_mul {n1 n2 : Nat} (c : ℝ)
    (F : Finset (Fin n1 × Fin n2) → ℝ) :
    rademacherExpectation (fun eps => c * F eps) = c * rademacherExpectation F := by
  unfold rademacherExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eps _
  ring

/-- rademacherExpectation of a nonneg function is nonneg. -/
lemma bridge_rademacherExpectation_nonneg {n1 n2 : Nat}
    (F : Finset (Fin n1 × Fin n2) → ℝ) (hF : ∀ eps, 0 ≤ F eps) :
    0 ≤ rademacherExpectation F := by
  unfold rademacherExpectation
  apply Finset.sum_nonneg
  intro eps _
  apply mul_nonneg _ (hF eps)
  unfold rademacherObservationWeight
  positivity

-- ============ MAIN REDUCTION ============

theorem solution
    (hEven :
      ∀ (n : Nat), 1 ≤ n →
      ∀ {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ), 0 < p →
      ∀ X : RealMatrix n1 n2,
        rademacherExpectation
            (fun eps =>
              schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^
                (2 * n))
          ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
              max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
                  ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))) :
    ∃ C : ℝ, 0 < C ∧
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
          (C * Real.sqrt (q : ℝ) *
            max (sampledRowGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))
                (sampledColumnGramSchatten Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X (q : ℝ))) ^ q := by
  refine ⟨2 * Real.exp 1, by positivity, ?_⟩
  intro β hβ n₁ n₂ m q Omega X hq2 hqlog
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hpdef
  set nn : ℕ := (q + 1) / 2 with hnndef
  -- basic facts about nn and exponents
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hnn1 : 1 ≤ nn := by omega
  have hq_le_2nn : (q : ℝ) ≤ (2 * nn : ℝ) := by
    have : q ≤ 2 * nn := by omega
    exact_mod_cast this
  have h2nn_le_2q : (2 * nn : ℝ) ≤ 2 * (q : ℝ) := by
    have : 2 * nn ≤ 2 * q := by omega
    exact_mod_cast this
  have hq_pos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le one_pos hq1
  have h2nn_pos : (0 : ℝ) < (2 * nn : ℝ) := by positivity
  -- log bound: log(max n₁ n₂) ≤ q  (from q ≥ β log(...), β > 1)
  have hlogN : Real.log (↑(max n₁ n₂) : ℝ) ≤ (q : ℝ) := by
    rcases le_or_gt (Real.log (↑(max n₁ n₂) : ℝ)) 0 with hneg | hpos
    · linarith
    · have hβ1 : (1 : ℝ) ≤ β := by linarith
      calc Real.log (↑(max n₁ n₂) : ℝ)
          ≤ β * Real.log (↑(max n₁ n₂) : ℝ) := by nlinarith [le_of_lt hpos]
        _ ≤ (q : ℝ) := hqlog
  -- finrank of range ≤ n₁ ≤ max, hence its log ≤ q
  have hlogR : ∀ eps : Finset (Fin n₁ × Fin n₂),
      Real.log
        ((Module.finrank ℝ
          (LinearMap.range (Matrix.toEuclideanLin
            (rademacherSampledMatrix Omega eps p X))) : ℝ)) ≤ (q : ℝ) := by
    intro eps
    set S := rademacherSampledMatrix Omega eps p X
    have hrk : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin S)) ≤ max n₁ n₂ := by
      calc Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin S))
          ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n₁)) := Submodule.finrank_le _
        _ = n₁ := by simp
        _ ≤ max n₁ n₂ := le_max_left _ _
    have hrkR : (↑(Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin S))) : ℝ)
        ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hrk
    rcases Nat.eq_zero_or_pos (Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin S)))
      with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; linarith [hq1]
    · have : Real.log (↑(Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin S))) : ℝ)
          ≤ Real.log (↑(max n₁ n₂) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hpos
        · exact hrkR
      linarith [hlogN]
  -- abbreviations
  set Sof : Finset (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂ :=
    fun eps => rademacherSampledMatrix Omega eps p X with hSof
  -- STEP 1: pointwise  schatten q (Sof eps) ^ q ≤ (e ^ q) * (schatten 2nn (Sof eps) ^ q)
  have hstep1 : ∀ eps,
      schattenNorm (q : ℝ) (Sof eps) ^ q
        ≤ (Real.exp 1) ^ q * (schattenNorm (2 * nn : ℝ) (Sof eps) ^ q) := by
    intro eps
    have hsw := bridge_pointwise_sandwich (Sof eps) (q : ℝ) hq1 nn hnn1 hq_le_2nn (hlogR eps)
    have hnonneg : 0 ≤ schattenNorm (q : ℝ) (Sof eps) := bridge_schattenNorm_nonneg _ _
    have hpow : schattenNorm (q : ℝ) (Sof eps) ^ q
        ≤ (Real.exp 1 * schattenNorm (2 * nn : ℝ) (Sof eps)) ^ q :=
      pow_le_pow_left₀ hnonneg hsw q
    rw [mul_pow] at hpow
    exact hpow
  -- STEP 2: E[schatten q ^q] ≤ e^q · E[schatten 2nn ^ q]
  have hLHS_nonneg : ∀ eps, 0 ≤ schattenNorm (q : ℝ) (Sof eps) ^ q :=
    fun eps => pow_nonneg (bridge_schattenNorm_nonneg _ _) q
  have hstep2 :
      rademacherExpectation (fun eps => schattenNorm (q : ℝ) (Sof eps) ^ q)
        ≤ (Real.exp 1) ^ q *
            rademacherExpectation (fun eps => schattenNorm (2 * nn : ℝ) (Sof eps) ^ q) := by
    have hmono := rademacher_expectation_monotone
      (fun eps => schattenNorm (q : ℝ) (Sof eps) ^ q)
      (fun eps => (Real.exp 1) ^ q * (schattenNorm (2 * nn : ℝ) (Sof eps) ^ q))
      hstep1
    rw [bridge_rademacherExpectation_const_mul] at hmono
    exact hmono
  -- g = schatten 2nn (Sof ·), nonneg
  set g : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun eps => schattenNorm (2 * nn : ℝ) (Sof eps) with hg
  have hg_nonneg : ∀ eps, 0 ≤ g eps := fun eps => bridge_schattenNorm_nonneg _ _
  -- npow→rpow rewrites under the expectation
  have hEq_q : rademacherExpectation (fun eps => g eps ^ q)
      = rademacherExpectation (fun eps => Real.rpow (g eps) (q : ℝ)) := by
    unfold rademacherExpectation
    apply Finset.sum_congr rfl; intro eps _
    congr 1
    exact (Real.rpow_natCast (g eps) q).symm
  have hEq_2nn : rademacherExpectation (fun eps => Real.rpow (g eps) (2 * nn : ℝ))
      = rademacherExpectation (fun eps => g eps ^ (2 * nn)) := by
    unfold rademacherExpectation
    apply Finset.sum_congr rfl; intro eps _
    congr 1
    rw [show ((2 * nn : ℝ)) = ((2 * nn : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast (g eps) (2 * nn)
  -- STEP 3: Jensen
  have hstep3 :
      rademacherExpectation (fun eps => Real.rpow (g eps) (q : ℝ))
        ≤ Real.rpow
            (rademacherExpectation (fun eps => Real.rpow (g eps) (2 * nn : ℝ)))
            ((q : ℝ) / (2 * nn : ℝ)) :=
    rademacher_expectation_power_mean (q : ℝ) (2 * nn : ℝ) hq_pos hq_le_2nn g hg_nonneg
  have hp_nonneg : 0 ≤ p := by rw [hpdef]; positivity
  -- Combined LHS chain so far: E[schatten q ^q] ≤ e^q · (E[g^(2nn)])^(q/2nn)
  have hchain :
      rademacherExpectation (fun eps => schattenNorm (q : ℝ) (Sof eps) ^ q)
        ≤ (Real.exp 1) ^ q *
            Real.rpow
              (rademacherExpectation (fun eps => g eps ^ (2 * nn)))
              ((q : ℝ) / (2 * nn : ℝ)) := by
    refine le_trans hstep2 ?_
    -- e^q · E[g^q]  =  e^q · E[g^ᵣq] ≤ e^q · (E[g^ᵣ2nn])^(q/2nn) = e^q · (E[g^2nn])^(q/2nn)
    have hEge0 : 0 ≤ (Real.exp 1) ^ q := by positivity
    rw [show rademacherExpectation (fun eps => g eps ^ q)
        = rademacherExpectation (fun eps => Real.rpow (g eps) (q : ℝ)) from hEq_q]
    refine mul_le_mul_of_nonneg_left ?_ hEge0
    refine le_trans hstep3 ?_
    rw [hEq_2nn]
  rcases eq_or_lt_of_le hp_nonneg with hp0 | hp_pos
  · -- p = 0 : sampled matrix is 0, LHS = 0 ≤ RHS
    have hSzero : ∀ eps, Sof eps = (0 : RealMatrix n₁ n₂) := by
      intro eps
      rw [hSof]
      funext i j
      simp [rademacherSampledMatrix, ← hp0]
    have hLHS0 :
        rademacherExpectation (fun eps => schattenNorm (q : ℝ) (Sof eps) ^ q) = 0 := by
      have : ∀ eps, schattenNorm (q : ℝ) (Sof eps) ^ q = 0 := by
        intro eps
        rw [hSzero eps, bridge_schattenNorm_zero (q : ℝ) (by positivity)]
        exact zero_pow (by omega)
      rw [show (fun eps => schattenNorm (q : ℝ) (Sof eps) ^ q) = (fun _ => (0:ℝ)) from
        funext this]
      unfold rademacherExpectation
      simp
    rw [hLHS0]
    apply pow_nonneg
    apply mul_nonneg
    · apply mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · exact le_max_of_le_left (bridge_rowGS_nonneg _ _ hp_nonneg _ _)
  · -- 0 < p : full chain
    -- abbreviations
    set r : ℝ := sampledRowGramSchatten Omega p X (2 * nn : ℝ) with hr
    set c : ℝ := sampledColumnGramSchatten Omega p X (2 * nn : ℝ) with hc
    set Rq : ℝ := sampledRowGramSchatten Omega p X (q : ℝ) with hRq
    set Cq : ℝ := sampledColumnGramSchatten Omega p X (q : ℝ) with hCq
    set PC : ℝ := (Nat.factorial (2 * nn) : ℝ) / ((2 ^ nn : ℝ) * (Nat.factorial nn : ℝ))
      with hPC
    have hr0 : 0 ≤ r := bridge_rowGS_nonneg _ _ (le_of_lt hp_pos) _ _
    have hc0 : 0 ≤ c := bridge_colGS_nonneg _ _ (le_of_lt hp_pos) _ _
    have hRq0 : 0 ≤ Rq := bridge_rowGS_nonneg _ _ (le_of_lt hp_pos) _ _
    have hCq0 : 0 ≤ Cq := bridge_colGS_nonneg _ _ (le_of_lt hp_pos) _ _
    have hPC0 : 0 ≤ PC := by rw [hPC]; positivity
    have hmaxrc0 : 0 ≤ max r c := le_max_of_le_left hr0
    -- even-q: E[g^(2nn)] ≤ PC · max(r^(2nn), c^(2nn))
    have hEg0 : 0 ≤ rademacherExpectation (fun eps => g eps ^ (2 * nn)) :=
      bridge_rademacherExpectation_nonneg _ (fun eps => pow_nonneg (hg_nonneg eps) _)
    have hevenq := hEven nn hnn1 Omega p hp_pos X
    -- g eps = schatten (2*nn) (Sof eps) = schatten (2*nn) (rademacherSampledMatrix ...)
    -- the even-q LHS matches E[g^(2nn)] definitionally
    have hMrc : max (r ^ (2 * nn)) (c ^ (2 * nn)) = (max r c) ^ (2 * nn) := by
      rcases le_total r c with hrc | hrc
      · rw [max_eq_right hrc, max_eq_right (pow_le_pow_left₀ hr0 hrc _)]
      · rw [max_eq_left hrc, max_eq_left (pow_le_pow_left₀ hc0 hrc _)]
    -- chain even-q into hchain's RHS inner expectation
    have hEbound : rademacherExpectation (fun eps => g eps ^ (2 * nn))
        ≤ PC * (max r c) ^ (2 * nn) := by
      calc rademacherExpectation (fun eps => g eps ^ (2 * nn))
          ≤ PC * max (r ^ (2 * nn)) (c ^ (2 * nn)) := hevenq
        _ = PC * (max r c) ^ (2 * nn) := by rw [hMrc]
    -- raise to (q/2nn) via rpow monotone
    have hqexp_pos : 0 ≤ (q : ℝ) / (2 * nn : ℝ) := by positivity
    have hPCrc0 : 0 ≤ PC * (max r c) ^ (2 * nn) := mul_nonneg hPC0 (pow_nonneg hmaxrc0 _)
    have hrpow_mono :
        Real.rpow (rademacherExpectation (fun eps => g eps ^ (2 * nn)))
            ((q : ℝ) / (2 * nn : ℝ))
          ≤ Real.rpow (PC * (max r c) ^ (2 * nn)) ((q : ℝ) / (2 * nn : ℝ)) :=
      Real.rpow_le_rpow hEg0 hEbound hqexp_pos
    -- Combine with hchain
    refine le_trans hchain ?_
    have heq0 : 0 ≤ (Real.exp 1) ^ q := by positivity
    have hstep_a :
        (Real.exp 1) ^ q *
          Real.rpow (rademacherExpectation (fun eps => g eps ^ (2 * nn)))
            ((q : ℝ) / (2 * nn : ℝ))
        ≤ (Real.exp 1) ^ q *
          Real.rpow (PC * (max r c) ^ (2 * nn)) ((q : ℝ) / (2 * nn : ℝ)) :=
      mul_le_mul_of_nonneg_left hrpow_mono heq0
    refine le_trans hstep_a ?_
    -- Now pure rpow algebra:  e^q · (PC·(max r c)^(2nn))^(q/2nn) ≤ (2e√q·max(Rq,Cq))^q
    have h2nn_ne : (2 * nn : ℝ) ≠ 0 := by positivity
    -- (1) split the product rpow
    have hsplit : Real.rpow (PC * (max r c) ^ (2 * nn)) ((q : ℝ) / (2 * nn : ℝ))
        = Real.rpow PC ((q : ℝ) / (2 * nn : ℝ))
          * Real.rpow ((max r c) ^ (2 * nn)) ((q : ℝ) / (2 * nn : ℝ)) :=
      Real.mul_rpow hPC0 (pow_nonneg hmaxrc0 _)
    -- (2) ((max r c)^(2nn))^(q/2nn) = (max r c)^q
    have hmaxpow : Real.rpow ((max r c) ^ (2 * nn)) ((q : ℝ) / (2 * nn : ℝ))
        = Real.rpow (max r c) (q : ℝ) := by
      have e1 : ((max r c) ^ (2 * nn) : ℝ) = Real.rpow (max r c) ((2 * nn : ℕ) : ℝ) :=
        (Real.rpow_natCast (max r c) (2 * nn)).symm
      have e2 : Real.rpow (Real.rpow (max r c) ((2 * nn : ℕ) : ℝ)) ((q : ℝ) / (2 * nn : ℝ))
          = Real.rpow (max r c) ((((2 * nn : ℕ) : ℝ)) * ((q : ℝ) / (2 * nn : ℝ))) :=
        (Real.rpow_mul hmaxrc0 (((2 * nn : ℕ) : ℝ)) ((q : ℝ) / (2 * nn : ℝ))).symm
      have e3 : (((2 * nn : ℕ) : ℝ)) * ((q : ℝ) / (2 * nn : ℝ)) = (q : ℝ) := by
        push_cast; field_simp
      rw [e1, e2, e3]
    -- (3) PC^(q/2nn) = (PC^(1/2nn))^q ≤ (2√q)^q
    have hPCsplit : Real.rpow PC ((q : ℝ) / (2 * nn : ℝ))
        = Real.rpow (Real.rpow PC ((1:ℝ) / (2 * nn : ℝ))) (q : ℝ) := by
      have e2 : Real.rpow (Real.rpow PC ((1:ℝ) / (2 * nn : ℝ))) (q : ℝ)
          = Real.rpow PC (((1:ℝ) / (2 * nn : ℝ)) * (q : ℝ)) :=
        (Real.rpow_mul hPC0 ((1:ℝ) / (2 * nn : ℝ)) (q : ℝ)).symm
      rw [e2]
      congr 1
      field_simp
    have hdf := buchholz_double_factorial_constant_bound nn hnn1
    -- bridge (c) gives PC^(1/2nn) ≤ √2·√(2nn);  and √2·√(2nn) ≤ 2√q
    have hPCbase0 : 0 ≤ Real.rpow PC ((1:ℝ) / (2 * nn : ℝ)) := Real.rpow_nonneg hPC0 _
    have hsqrt_le : Real.sqrt 2 * Real.sqrt (2 * nn : ℝ) ≤ 2 * Real.sqrt (q : ℝ) := by
      have h1 : Real.sqrt 2 * Real.sqrt (2 * nn : ℝ) = 2 * Real.sqrt (nn : ℝ) := by
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        rw [show (2 : ℝ) * (2 * nn : ℝ) = 4 * nn by ring]
        rw [show (4 : ℝ) * nn = (2:ℝ)^2 * nn by ring, Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by norm_num)]
      rw [h1]
      have hnnq : (nn : ℝ) ≤ (q : ℝ) := by
        have : nn ≤ q := by omega
        exact_mod_cast this
      have := Real.sqrt_le_sqrt hnnq
      linarith
    have hPCval : Real.rpow PC ((1:ℝ) / (2 * nn : ℝ)) ≤ 2 * Real.sqrt (q : ℝ) :=
      le_trans hdf hsqrt_le
    have h2sqrtq0 : 0 ≤ 2 * Real.sqrt (q : ℝ) := by positivity
    have hPCpow_le : Real.rpow (Real.rpow PC ((1:ℝ) / (2 * nn : ℝ))) (q : ℝ)
        ≤ Real.rpow (2 * Real.sqrt (q : ℝ)) (q : ℝ) :=
      Real.rpow_le_rpow hPCbase0 hPCval (le_of_lt hq_pos)
    -- (4) max r c ≤ max Rq Cq via antitone
    have hr_le : r ≤ Rq := by
      rw [hr, hRq]
      exact sampled_row_gram_schatten_antitone_exp Omega p (le_of_lt hp_pos) X (q:ℝ) (2*nn:ℝ) hq1 hq_le_2nn
    have hc_le : c ≤ Cq := by
      rw [hc, hCq]
      exact sampled_column_gram_schatten_antitone_exp Omega p (le_of_lt hp_pos) X (q:ℝ) (2*nn:ℝ) hq1 hq_le_2nn
    have hmax_le : max r c ≤ max Rq Cq := max_le_max hr_le hc_le
    have hmaxRqCq0 : 0 ≤ max Rq Cq := le_max_of_le_left hRq0
    have hmaxpow_le : Real.rpow (max r c) (q : ℝ) ≤ Real.rpow (max Rq Cq) (q : ℝ) :=
      Real.rpow_le_rpow hmaxrc0 hmax_le (le_of_lt hq_pos)
    -- assemble:  e^q · PC^(q/2nn) · (max r c)^q ≤ e^q · (2√q)^q · (max Rq Cq)^q
    have heq0 : 0 ≤ (Real.exp 1) ^ q := by positivity
    calc (Real.exp 1) ^ q *
            Real.rpow (PC * (max r c) ^ (2 * nn)) ((q : ℝ) / (2 * nn : ℝ))
        = (Real.exp 1) ^ q *
            (Real.rpow PC ((q : ℝ) / (2 * nn : ℝ)) * Real.rpow (max r c) (q : ℝ)) := by
          rw [hsplit, hmaxpow]
      _ = (Real.exp 1) ^ q *
            (Real.rpow (Real.rpow PC ((1:ℝ) / (2 * nn : ℝ))) (q : ℝ)
              * Real.rpow (max r c) (q : ℝ)) := by rw [hPCsplit]
      _ ≤ (Real.exp 1) ^ q *
            (Real.rpow (2 * Real.sqrt (q : ℝ)) (q : ℝ) * Real.rpow (max Rq Cq) (q : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ heq0
          apply mul_le_mul hPCpow_le hmaxpow_le (Real.rpow_nonneg hmaxrc0 _)
          exact Real.rpow_nonneg h2sqrtq0 _
      _ = Real.rpow (2 * Real.exp 1 * Real.sqrt (q : ℝ) * max Rq Cq) (q : ℝ) := by
          have he : (Real.exp 1) ^ q = Real.rpow (Real.exp 1) (q : ℝ) :=
            (Real.rpow_natCast (Real.exp 1) q).symm
          -- e^ᵣq · ((2√q)^ᵣq · (maxRqCq)^ᵣq) = (e·2√q·maxRqCq)^ᵣq
          have hm1 : Real.rpow (2 * Real.sqrt (q:ℝ)) (q:ℝ) * Real.rpow (max Rq Cq) (q:ℝ)
              = Real.rpow ((2 * Real.sqrt (q:ℝ)) * (max Rq Cq)) (q:ℝ) :=
            (Real.mul_rpow h2sqrtq0 hmaxRqCq0).symm
          have hm2 : Real.rpow (Real.exp 1) (q:ℝ)
                * Real.rpow ((2 * Real.sqrt (q:ℝ)) * (max Rq Cq)) (q:ℝ)
              = Real.rpow (Real.exp 1 * ((2 * Real.sqrt (q:ℝ)) * (max Rq Cq))) (q:ℝ) :=
            (Real.mul_rpow (le_of_lt (Real.exp_pos 1))
              (mul_nonneg h2sqrtq0 hmaxRqCq0)).symm
          rw [he, hm1, hm2]
          congr 1
          ring
      _ = (2 * Real.exp 1 * Real.sqrt (q : ℝ) * max Rq Cq) ^ q :=
          Real.rpow_natCast _ q

