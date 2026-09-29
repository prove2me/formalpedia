-- Prove2me | solution 1 for TreatmentLocality.asymptotic_efficiency_of_information_sharing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T00:03:16.971358+00:00
-- url     : https://prove2.me/submissions/f9a11708-cc08-4e8c-91f4-fc6538525115
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Statistics_information_inequality
import Theorems.Thm_TreatmentLocality_exists_least_favorable_score_of_unbiased

open MeasureTheory ProbabilityTheory Filter TreatmentLocality
open scoped NNReal ENNReal Topology

theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (huni : MarkovChainCLT.UniformlyErgodic (expKernel M) ν)
    (δ : (T : ℕ) → (Fin T → Step S) → S → ℝ)
    (hmeas : ∀ T s, Measurable (fun path => δ T path s))
    (hL2 : ∀ T s, MemLp (fun ω : ℕ → Step S => δ T (fun i => ω (i.1 + 1)) s) 2
      (MarkovChainCLT.chainMeasure (expKernel M) ν))
    (hunbiased : ∀ (M' : Model S), M'.crucial = M.crucial → M'.γdisc = M.γdisc →
      (∃ m' : S → Bool → ℝ, M'.GaussianRewards m' v) →
      ∀ (ν' : Measure (Step S)) (_ : IsProbabilityMeasure ν'),
        Kernel.Invariant (expKernel M') ν' →
        MarkovChainCLT.UniformlyErgodic (expKernel M') ν' →
        ∀ T : ℕ, 1 ≤ T → ∀ s,
          ∫ ω, δ T (fun i => ω (i.1 + 1)) s
            ∂(MarkovChainCLT.chainMeasure (expKernel M') ν') = M'.ate s) :
    ∀ w : S → ℝ, ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℕ in atTop,
      ∑ s, ∑ s', w s * mbISCov M ν s s' * w s'
        ≤ (T : ℝ) *
          (∫ ω, (∑ s, w s * δ T (fun i => ω (i.1 + 1)) s
              - ∫ ω', ∑ s, w s * δ T (fun i => ω' (i.1 + 1)) s
                  ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)) ^ 2
            ∂(MarkovChainCLT.chainMeasure (expKernel M) ν)) + ε := by
  classical
  intro w ε hε
  set P := MarkovChainCLT.chainMeasure (expKernel M) ν with hP
  set Q := ∑ s, ∑ s', w s * mbISCov M ν s s' * w s' with hQdef
  -- the linear combination of the estimator coordinates
  set D : ℕ → (ℕ → Step S) → ℝ :=
    fun T ω => ∑ s, w s * δ T (fun i => ω (i.1 + 1)) s with hD
  have hDmem : ∀ T, MemLp (D T) 2 P := fun T =>
    memLp_finsetSum (μ := P) (p := 2) Finset.univ
      (f := fun s ω => w s * δ T (fun i => ω (i.1 + 1)) s)
      fun s _ => (hL2 T s).const_mul (w s)
  have hV : ∀ T : ℕ, 0 ≤ ∫ ω, (D T ω - ∫ ω', D T ω' ∂P) ^ 2 ∂P :=
    fun T => integral_nonneg fun ω => sq_nonneg _
  by_cases hQ0 : Q ≤ 0
  · -- degenerate direction: the bound is trivial
    refine Eventually.of_forall fun T => ?_
    have := hV T
    have hT : (0:ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    nlinarith [mul_nonneg hT (hV T)]
  · push_neg at hQ0
    obtain ⟨κ, hκ0, hscore⟩ :=
      TreatmentLocality.exists_least_favorable_score_of_unbiased M m v hgauss hpos ν hinv huni
        δ hmeas hL2 hunbiased w
    filter_upwards [eventually_ge_atTop (⌈Q * κ / ε⌉₊ + 1)] with T hT
    have hT1 : 1 ≤ T := le_trans (Nat.le_add_left 1 _) hT
    obtain ⟨g, hgmem, hg0, hgcov, hgsq⟩ := hscore T hT1
    -- Cramér–Rao: `Q² = (∫ D g)² ≤ Var(D) · ∫ g² ≤ Var(D) · (T + κ) Q`
    have hinfo := Statistics.information_inequality P (D T) g (hDmem T) hgmem hg0
    rw [hgcov] at hinfo
    set V := ∫ ω, (D T ω - ∫ ω', D T ω' ∂P) ^ 2 ∂P with hVdef
    have hstep : Q ^ 2 ≤ V * (((T : ℝ) + κ) * Q) :=
      hinfo.trans (mul_le_mul_of_nonneg_left hgsq (hV T))
    have hQle : Q ≤ V * ((T : ℝ) + κ) := by
      have h := hstep
      nlinarith [hQ0]
    -- the arithmetic tail: `Q κ ≤ ε T` once `T ≥ ⌈Qκ/ε⌉ + 1`
    have hTr : Q * κ / ε ≤ (T : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      exact_mod_cast le_trans (Nat.le_succ _) hT
    have hQκ : Q * κ ≤ ε * (T : ℝ) := by
      rw [div_le_iff₀ hε] at hTr; linarith
    have hTpos : (0:ℝ) < (T : ℝ) := by
      have : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT1
      linarith
    have hTk : (0:ℝ) < (T : ℝ) + κ := by linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_le_mul_of_nonneg_left hQle hTpos.le,
      mul_pos (sub_pos.mpr hcon) hTk, hQκ, mul_nonneg hε.le hκ0]
