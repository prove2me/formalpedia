-- Prove2me | solution 1 for mme_omega_le_of_subrank_capacity_poly
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T20:01:49.928574+00:00
-- url     : https://prove2.me/submissions/a369d5ab-a2f9-4927-ae36-6f77ea5ef0be

import Definitions.Def_mme_subrank_capacity_poly
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_omega_strassen
import Definitions.Def_mme_omega_pos
import Theorems.Thm_mme_subrankCapacityPoly_witness
import Theorems.Thm_mme_borderRank_kronPow_le
import Theorems.Thm_mme_degenerates_asymptoticRank_le
import Theorems.Thm_mme_asymptotic_sum_inequality
import Theorems.Thm_mme_holder_subexp_capacity_omega_bound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Basic

open MME PiTensorProduct BigOperators Filter Topology

universe u

namespace MME

/-- Composition lemma (inline helper, kept private to this file): given a restriction
`Restrict X Y` and a degeneration `Degenerates Y Z`, we get `Degenerates X Z`. -/
private theorem omegaPolyAux_degenerates_of_restrict_left
    {K : Type u} [Field K] {d : ℕ} {X Y Z : TensorObj K d}
    (hRes : TensorObj.Restrict X Y) (hDeg : Degenerates Y Z) :
    Degenerates X Z := by
  obtain ⟨f, hf⟩ := hRes
  obtain ⟨h, Φ, hvan, hcoeff⟩ := hDeg
  -- Build a new poly family by post-composing each map with f.
  refine ⟨h,
    ⟨fun i => (Φ.A i).mapRange (fun L => (f i).comp L) (by simp)⟩, ?_, ?_⟩
  · -- Vanishing of coefficients below h.
    intro k hk
    have hco :
        (PolyFamily.mk fun i => (Φ.A i).mapRange (fun L => (f i).comp L) (by simp) :
          PolyFamily X Z).coeff k =
            PiTensorProduct.map f (Φ.coeff k) := by
      unfold PolyFamily.coeff
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.mapRange_apply]
      rw [show (fun i => (f i).comp (Φ.A i (j i))) =
            (fun i => (f i).comp ((fun i => Φ.A i (j i)) i)) from rfl,
          PiTensorProduct.map_comp]
      rfl
    rw [hco, hvan k hk, map_zero]
  · -- Coefficient at h equals X.t.
    have hco :
        (PolyFamily.mk fun i => (Φ.A i).mapRange (fun L => (f i).comp L) (by simp) :
          PolyFamily X Z).coeff h =
            PiTensorProduct.map f (Φ.coeff h) := by
      unfold PolyFamily.coeff
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.mapRange_apply]
      rw [show (fun i => (f i).comp (Φ.A i (j i))) =
            (fun i => (f i).comp ((fun i => Φ.A i (j i)) i)) from rfl,
          PiTensorProduct.map_comp]
      rfl
    rw [hco, hcoeff, hf]

end MME

/-- **The abstract ω-bound from polynomial-witness subrank capacity.**

For any order-3 tensor `T` admitting a border-rank bound and a
polynomial-witness subrank capacity lower bound:

  `Degenerates T (diagObj K 3 r)  ∧  (r : ℝ) ≤ R  ∧  1 ≤ R  ∧  1 < V  ∧
   V ≤ subrankCapacityPoly T   ⇒   ω  ≤  log R / log V`. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {R V : ℝ} {r : ℕ}
    (hR : Degenerates T (TensorObj.diagObj K 3 r))
    (hRcast : (r : ℝ) ≤ R) (hRpos : 1 ≤ R)
    (hV : 1 < V) (hsub : V ≤ subrankCapacityPoly T) :
    matMulExp_strassen K ≤ Real.log R / Real.log V := by
  -- Set up positivity / monotonicity facts.
  set ω := matMulExp_strassen K with hω_def
  have hω1 : (1 : ℝ) ≤ ω := MME.one_le_matMulExp_strassen
  have hω_pos : 0 < ω := lt_of_lt_of_le zero_lt_one hω1
  have hVpos : 0 < V := lt_trans zero_lt_one hV
  have hRpos' : 0 < R := lt_of_lt_of_le zero_lt_one hRpos
  have hlogV_pos : 0 < Real.log V := Real.log_pos hV
  have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hRpos
  have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  -- Reduce to `ω * log V ≤ log R`.
  rw [le_div_iff₀ hlogV_pos]
  -- Step 1: For every `δ ∈ (0, V - 1)`, `ω * log (V - δ) ≤ log R`.
  have key : ∀ δ : ℝ, 0 < δ → δ < V - 1 → ω * Real.log (V - δ) ≤ Real.log R := by
    intro δ hδ_pos hδ_small
    have hVδ_gt1 : 1 < V - δ := by linarith
    have hVδ_pos : 0 < V - δ := lt_trans zero_lt_one hVδ_gt1
    -- Apply the witness extraction.
    obtain ⟨V', hV'gt, hV'one, c, hcV'⟩ :=
      mme_subrankCapacityPoly_witness (T := T) hV hsub hδ_pos
    have hV'_gt1 : 1 < V' := lt_trans hVδ_gt1 hV'gt
    have hV'_pos : 0 < V' := lt_trans zero_lt_one hV'_gt1
    -- Apply Hölder's lemma at V'.
    have h_holder : ω * Real.log V' ≤ Real.log R := by
      apply mme_holder_subexp_capacity_omega_bound hω1 hV'_gt1 hRpos
      refine ⟨c, ?_⟩
      intro ε hε
      have h_nat : ∃ᶠ (N : ℕ) in atTop,
          ∃ (k : ℕ) (a b c' : Fin k → ℕ),
            (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
            TensorObj.Restrict
              (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
              (T.kronPow N) ∧
            V' ^ N * (1 - ε) ≤
              ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := hcV' ε hε
      -- Convert the ℕ-frequency to ℝ-frequency via `Tendsto.frequently_map`.
      apply Tendsto.frequently_map (f := ((↑) : ℕ → ℝ))
        tendsto_natCast_atTop_atTop _ h_nat
      rintro N ⟨k, a, b, c', hk_bound, hRestrict, hVN_le⟩
      -- The per-N conversion: build a real witness from the natural witness at N.
      refine ⟨k, fun i => ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3),
        ?_, ?_, ?_, ?_⟩
      · -- (k : ℝ) ≤ ((N : ℕ) + 1 : ℝ)^c — same as hk_bound after casting.
        simpa using hk_bound
      · -- nonneg
        intro i
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · -- V'^(N : ℝ) * (1 - ε) ≤ ∑ x_i
        have h_rpow_eq : (V' : ℝ) ^ ((N : ℕ) : ℝ) = (V' : ℝ) ^ (N : ℕ) :=
          Real.rpow_natCast V' N
        rw [h_rpow_eq]
        exact hVN_le
      · -- ∑ (x_i)^ω ≤ R^(N : ℝ)
        -- Step A: Restriction-composes-with-degeneration.
        have hDegT : Degenerates (T.kronPow N) (TensorObj.diagObj K 3 (r ^ N)) :=
          mme_borderRank_kronPow_le T N r hR
        have hDegBigAdd :
            Degenerates
              (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
              (TensorObj.diagObj K 3 (r ^ N)) :=
          MME.omegaPolyAux_degenerates_of_restrict_left hRestrict hDegT
        -- Step B: AR ≤ r^N
        have hAR_le : tensorAsymptoticRank
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i))) ≤ (r ^ N : ℕ) :=
          mme_degenerates_asymptoticRank_le hDegBigAdd
        -- Step C: Apply the τ theorem.
        have hSum_le_rN :
            ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ (ω / 3) ≤ ((r ^ N : ℕ) : ℝ) :=
          mme_asymptotic_sum_inequality (K := K) a b c' (r ^ N) hAR_le
        -- Step D: r^N ≤ R^N (real, natural-pow), then ≤ R^(N:ℝ).
        have hrN_le_RN : ((r ^ N : ℕ) : ℝ) ≤ (R : ℝ) ^ N := by
          rw [Nat.cast_pow]
          exact pow_le_pow_left₀ hr_nn hRcast N
        -- Step E: convert the LHS to use `((x)^(1/3))^ω` form.
        have hsum_rw :
            ∑ i, (((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) ^ ω =
              ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ (ω / 3) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [← Real.rpow_mul (Nat.cast_nonneg _)]
          congr 1
          ring
        -- Combine: ∑ ((x)^(1/3))^ω = ∑ x^(ω/3) ≤ r^N ≤ R^N = R^(N:ℝ).
        rw [hsum_rw]
        calc ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ (ω / 3)
            ≤ ((r ^ N : ℕ) : ℝ) := hSum_le_rN
          _ ≤ (R : ℝ) ^ N := hrN_le_RN
          _ = (R : ℝ) ^ ((N : ℕ) : ℝ) := (Real.rpow_natCast R N).symm
    -- Bridge: V - δ ≤ V', so log(V - δ) ≤ log V', so ω·log(V-δ) ≤ ω·log V' ≤ log R.
    have hlog_le : Real.log (V - δ) ≤ Real.log V' :=
      Real.log_le_log hVδ_pos hV'gt.le
    calc ω * Real.log (V - δ)
        ≤ ω * Real.log V' := by
          exact mul_le_mul_of_nonneg_left hlog_le (le_of_lt hω_pos)
      _ ≤ Real.log R := h_holder
  -- Step 2: take δ → 0. Use sequence δ_n := (V - 1) / (n + 2) → 0.
  -- Define `f n := (V - 1) / ((n : ℝ) + 2)` for n : ℕ.
  set δseq : ℕ → ℝ := fun n => (V - 1) / ((n : ℝ) + 2) with hδseq_def
  have hVm1_pos : 0 < V - 1 := by linarith
  have hδ_pos : ∀ n, 0 < δseq n := by
    intro n
    apply div_pos hVm1_pos
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hδ_small : ∀ n, δseq n < V - 1 := by
    intro n
    rw [hδseq_def]
    have hden : (1 : ℝ) < (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hden_pos : 0 < (n : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ hden_pos]
    nlinarith [hVm1_pos]
  -- Pointwise bound from `key`.
  have hpt : ∀ n, ω * Real.log (V - δseq n) ≤ Real.log R := by
    intro n
    exact key (δseq n) (hδ_pos n) (hδ_small n)
  -- δseq → 0.
  have hδ_tend : Tendsto δseq atTop (𝓝 0) := by
    -- (V-1) / ((n : ℝ) + 2) → 0
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop := by
      have hbase : Tendsto (fun n : ℕ => ((n : ℝ))) atTop atTop :=
        tendsto_natCast_atTop_atTop
      exact tendsto_atTop_add_const_right atTop 2 hbase
    have h2 : Tendsto (fun n : ℕ => (V - 1) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop h1
    exact h2
  -- V - δseq n → V.
  have hVmδ_tend : Tendsto (fun n => V - δseq n) atTop (𝓝 V) := by
    have : Tendsto (fun n => V - δseq n) atTop (𝓝 (V - 0)) :=
      (tendsto_const_nhds (x := V)).sub hδ_tend
    simpa using this
  -- log (V - δseq n) → log V (continuity of log at V > 0).
  have hlogV_tend : Tendsto (fun n => Real.log (V - δseq n)) atTop (𝓝 (Real.log V)) :=
    (Real.continuousAt_log (ne_of_gt hVpos)).tendsto.comp hVmδ_tend
  -- ω * log(V - δseq n) → ω * log V.
  have hgoal_tend : Tendsto (fun n => ω * Real.log (V - δseq n)) atTop
      (𝓝 (ω * Real.log V)) :=
    hlogV_tend.const_mul ω
  -- Conclude via le_of_tendsto.
  exact le_of_tendsto hgoal_tend (Eventually.of_forall hpt)
