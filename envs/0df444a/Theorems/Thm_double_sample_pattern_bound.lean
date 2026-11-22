-- Prove2me | Theorems.Thm_double_sample_pattern_bound
-- name    : double_sample_pattern_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:39.790949+00:00
-- url     : https://prove2.me/theorems/e7e94489-3e41-4178-941a-120069b34b33
-- title:
--   double sample pattern bound: double sample pattern bound
-- statement:
--   On the double sample, the probability that any hypothesis has
--       EmpErr' - EmpErr ≥ ε/2 is bounded by GF(C,2m) · exp(-mε²/8).
--
--       **Proof strategy (Approach A — standard exchangeability, 5 steps):**
--
--       1. **EXCHANGEABILITY:** Under D^m ⊗ D^m, the 2m draws z₁,...,z_{2m} are iid from D.
--          The joint distribution is invariant under permutations of {1,...,2m}.
--
--          Key lemma: P_{D^m⊗D^m}[event(S,S')] = E_z[P_{split}[event | z]]
--          where z = merged sample and the split is uniformly random among all
--          C(2m,m) ways to partition z into two groups of m.
--
--          ```
--          -- Measure.pi permutation invariance
--          have pi_perm_invariant : ∀ (σ : Equiv.Perm (Fin (2*m))),
--            (Measure.pi (fun _ : Fin (2*m) => D)).map (fun z i => z (σ i))
--            = Measure.pi (fun _ : Fin (2*m) => D) := by ...
--          -- Consequence: the event probability equals the split-averaged probability
--          have exchangeability :
--            DoubleSampleMeasure D m {p | ∃ h ∈ C, gap(p) ≥ ε/2}
--            = ∫ z, SplitMeasure m {vs | ∃ h ∈ C, gap(split z vs) ≥ ε/2}
--              ∂(Measure.pi (fun _ : Fin (2*m) => D)) := by ...
--          ```
--
--       2. **CONDITIONING:** For fixed merged sample z of 2m points:
--          - C restricts to at most GF(C,2m) distinct labeling patterns on z (deterministic).
--          - For each pattern p, define:
--            diff(p, split) = EmpErr_{S'}(p) - EmpErr_S(p)
--            = (1/m) ∑_{i∈S'} a_i - (1/m) ∑_{i∈S} a_i
--            where a_i = 1[pattern(z_i) ≠ c(z_i)] ∈ {0,1}.
--
--          ```
--          -- Number of distinct patterns
--          have num_patterns : ∀ (z : MergedSample X m),
--            Set.ncard {p : Fin (2*m) → Bool | ∃ h ∈ C, ∀ i, p i = (h (z i) ≠ c (z i))}
--            ≤ GrowthFunction X C (2*m) := by ...
--          ```
--
--       3. **PER-PATTERN HOEFFDING ON SPLITS:** For fixed z and fixed pattern p:
--          Under uniformly random split (S,S') of z into two groups of m:
--          diff(p, split) = (1/m) ∑_{i∈S'} a_i - (1/m) ∑_{i∈S} a_i
--
--          This is a function of the random partition. By Hoeffding's inequality for
--          sampling without replacement (Serfling 1974):
--          P_split[diff ≥ ε/2] ≤ exp(-mε²/8)
--
--          Alternative derivation: Hoeffding without replacement from Hoeffding with
--          replacement (iid signs) via coupling. The without-replacement bound is
--          actually TIGHTER (variance reduction), but the with-replacement bound suffices.
--
--          ```
--          -- Per-pattern concentration
--          have per_pattern_bound : ∀ (z : MergedSample X m) (a : Fin (2*m) → ℝ)
--            (ha : ∀ i, a i ∈ Set.Icc 0 1),
--            SplitMeasure m {vs | (1/m) * ∑ i ∈ second_group vs, a i
--              - (1/m) * ∑ i ∈ first_group vs, a i ≥ ε/2}
--            ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * (ε/2)^2 / 2)) := by ...
--          -- Note: m*(ε/2)^2 / 2 = mε²/8
--          ```
--
--       4. **UNION BOUND:** P_split[∃ pattern: diff ≥ ε/2 | z]
--          ≤ (number of patterns) · max_pattern P_split[diff ≥ ε/2]
--          ≤ GF(C,2m) · exp(-mε²/8)
--
--          ```
--          have union_bound : ∀ (z : MergedSample X m),
--            SplitMeasure m {vs | ∃ h ∈ C, gap(split z vs, h) ≥ ε/2}
--            ≤ ENNReal.ofReal (GrowthFunction X C (2*m) * Real.exp (-(m : ℝ) * ε^2 / 8))
--            := by ...
--          ```
--
--       5. **INTEGRATE:** P_{D^m⊗D^m}[event]
--          = E_z[P_split[event|z]]                      (by step 1)
--          ≤ E_z[GF(C,2m) · exp(-mε²/8)]               (by step 4, pointwise)
--          = GF(C,2m) · exp(-mε²/8)                     (bound is independent of z)
--
--          ```
--          -- The bound is a constant, so integrating gives the same constant
--          -- (using IsProbabilityMeasure for the 2m-fold product)
--          ```
--
--       **Infrastructure needed:**
--       - `Fin.sumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)` (available in Mathlib)
--       - `mergeSamples` / `splitMergedSample` (defined above)
--       - `SplitMeasure` and `ValidSplit` (defined above)
--       - `Measure.pi` permutation invariance (to be proved or imported)
--       - Hoeffding for sampling without replacement
--       - `GrowthFunction` on 2m points + `sauer_shelah_exp_bound` from Rademacher.lean
--
--       **MEASURABILITY CONCERNS:**
--       - The merged sample z ↦ P_split[event|z] must be measurable as a function of z.
--         Since the event is a finite union over patterns, and each pattern's indicator
--         is a measurable function of z (finite evaluation), this follows.
--       - `GrowthFunction X C (2*m)` is a natural number (deterministic), no measurability issue.
--
--       **References:** SSBD Theorem 6.7, Hoeffding (1963), Serfling (1974)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1021-L1090
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1021-L1090

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal

theorem double_sample_pattern_bound {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
      (MeasureTheory.Measure.pi (fun _ : Fin m => D))
    {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
      EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
    ≤ ENNReal.ofReal (↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by sorry
