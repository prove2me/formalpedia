-- Prove2me | solution 1 for freeEnergy_le_lse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:09:35.132738+00:00
-- url     : https://prove2.me/submissions/06c7af9c-7198-419c-8e25-b376d0e041e4

-- Sol generated from Bridges/LogSumExpVariational.lean
import Mathlib
import Definitions.Def_Bridges_LogSumExpVariational
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Log-Sum-Exp Variational Formula (Gibbs Variational Principle)

This file proves the finite-dimensional Gibbs variational principle:

  τ * log (∑ᵢ exp(xᵢ/τ)) = sup { ∑ᵢ pᵢxᵢ + τ * H(p) | p ∈ Δₙ }

where H(p) = -∑ᵢ pᵢ log pᵢ is Shannon entropy and Δₙ is the probability simplex.

The proof proceeds via the KL-divergence route:
1. Show that the free energy objective equals τ log Z minus τ * KL(p ∥ q)
   where q is the softmax/Gibbs distribution.
2. Use log x ≤ x - 1 to establish KL nonnegativity.
3. Conclude the upper bound and attainment at the softmax distribution.

## Main Results

* `partitionFun_pos` — positivity of partition function
* `softmaxProb_isProbVec` — softmax defines a probability vector
* `freeEnergy_le_lse` — upper bound: free energy ≤ τ log Z
* `freeEnergy_eq_lse_at_softmax` — attainment at softmax
* `lse_variational_formula` — the exact supremum identity

## Cross-Domain Significance

This theorem connects:
- **Convex analysis**: log-sum-exp as convex conjugate of negative entropy
- **Information theory**: KL divergence nonnegativity
- **Statistical mechanics**: free energy variational principle
- **Machine learning**: softmax as entropy-regularized optimizer
- **Tropical geometry**: dequantization bridge (τ → 0⁺ limit gives max)
-/


open Finset BigOperators Real

/-! ## Section 1: Definitions -/






/-! ## Section 2: Basic Properties of Partition Function and Softmax -/

theorem partitionFun_pos {n : ℕ} (hn : 0 < n) (τ : ℝ) (x : Fin n → ℝ) :
    0 < partitionFun τ x := by
  exact Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ⟨ ⟨ 0, hn ⟩, Finset.mem_univ _ ⟩

theorem softmaxProb_pos {n : ℕ} (hn : 0 < n) (τ : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    0 < softmaxProb τ x i := by
  exact div_pos ( Real.exp_pos _ ) ( partitionFun_pos hn τ x )


theorem softmaxProb_sum {n : ℕ} (hn : 0 < n) (τ : ℝ) (x : Fin n → ℝ) :
    ∑ i : Fin n, softmaxProb τ x i = 1 := by
  unfold softmaxProb;
  unfold partitionFun; rw [ ← Finset.sum_div _ _ _, div_self <| ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ⟨ ⟨ 0, hn ⟩, Finset.mem_univ _ ⟩ ] ;


/-
Log of softmax probability: log(qᵢ) = xᵢ/τ - log Z.
-/
theorem log_softmaxProb {n : ℕ} (hn : 0 < n) (τ : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    Real.log (softmaxProb τ x i) = x i / τ - Real.log (partitionFun τ x) := by
  unfold softmaxProb partitionFun;
  rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) ⟨ i, Finset.mem_univ _ ⟩ ), Real.log_exp ]

/-! ## Section 3: KL Divergence and Gibbs Inequality -/

/-
Scalar KL inequality: for u ≥ 0 and v > 0, u * log(u/v) ≥ u - v.
    This is the key analytic inequality underlying KL nonnegativity.
-/
theorem scalar_kl_ineq (u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v) :
    u - v ≤ (if u = 0 then 0 else u * Real.log (u / v)) := by
  by_cases hu0 : u = 0 <;> simp_all +decide;
  · grind +qlia;
  · have := Real.log_le_sub_one_of_pos ( div_pos hv ( lt_of_le_of_ne hu ( Ne.symm hu0 ) ) );
    rw [ Real.log_div ] at * <;> first | positivity | ring_nf at * ; nlinarith [ mul_inv_cancel₀ hu0 ] ;

/-
Finite Gibbs inequality (KL divergence nonnegativity):
    For probability vectors p and strictly positive q,
    ∑ᵢ pᵢ log(pᵢ/qᵢ) ≥ 0 (with 0 log 0 = 0 convention).
-/
theorem gibbs_inequality_finite {n : ℕ} (p q : Fin n → ℝ)
    (hp : IsProbVec p) (hq_pos : ∀ i, 0 < q i) (hq_sum : (∑ i, q i) = 1) :
    0 ≤ ∑ i, if p i = 0 then 0 else p i * Real.log (p i / q i) := by
  -- Applying the scalar_kl_ineq inequality for each i, we get p i - q i ≤ (if p i = 0 then 0 else p i * log (p i / q i)).
  have h_scalar : ∀ i, p i - q i ≤ (if p i = 0 then 0 else p i * Real.log (p i / q i)) := by
    exact fun i => by simpa [ * ] using scalar_kl_ineq ( p i ) ( q i ) ( hp.1 i ) ( hq_pos i ) ;
  exact le_trans ( by norm_num [ hp.2, hq_sum ] ) ( Finset.sum_le_sum fun i _ => h_scalar i )

/-! ## Section 4: Free Energy Upper Bound -/

/-
The free energy of any probability vector is at most τ * log Z.
    This is the upper bound half of the variational principle.
-/

/-! ## Section 5: Attainment at Softmax -/

/-
The free energy objective evaluated at the softmax distribution
    equals τ * log Z exactly.
-/


/-! ## Section 6: Supremum Formulation -/

/-
**Gibbs Variational Principle / Log-Sum-Exp Duality**:

    τ * log(∑ᵢ exp(xᵢ/τ)) = sup { ∑ᵢ pᵢxᵢ + τ H(p) | p is a probability vector }

    This is the finite-dimensional Legendre–Fenchel duality between log-sum-exp
    and negative Shannon entropy on the probability simplex.
-/


theorem solution{n : ℕ} (hn : 0 < n) (τ : ℝ) (hτ : 0 < τ) (x p : Fin n → ℝ)
    (hp : IsProbVec p) :
    freeEnergyObj τ x p ≤ τ * Real.log (partitionFun τ x) := by
  -- By definition of $freeEnergyObj$, we have
  have h_free_energy : freeEnergyObj τ x p = ∑ i, p i * x i - τ * (∑ i, if p i = 0 then 0 else p i * Real.log (p i)) := by
    unfold freeEnergyObj shannonEntropyTerm; ring;
  -- By definition of $softmaxProb$, we have
  have h_softmax : ∑ i, p i * (x i / τ - Real.log (partitionFun τ x)) = (∑ i, p i * x i) / τ - (∑ i, p i) * Real.log (partitionFun τ x) := by
    simp +decide only [mul_sub, sum_sub_distrib, sum_div, mul_div_assoc, sum_mul];
  have h_gibbs : ∑ i, (if p i = 0 then 0 else p i * Real.log (p i / softmaxProb τ x i)) ≥ 0 := by
    apply gibbs_inequality_finite p (softmaxProb τ x) hp (fun i => softmaxProb_pos hn τ x i) (softmaxProb_sum hn τ x);
  -- By definition of $softmaxProb$, we have $\log(p_i / softmaxProb τ x i) = \log(p_i) - \log(softmaxProb τ x i)$.
  have h_log_softmax : ∀ i, (if p i = 0 then 0 else p i * Real.log (p i / softmaxProb τ x i)) = (if p i = 0 then 0 else p i * Real.log (p i)) - p i * (x i / τ - Real.log (partitionFun τ x)) := by
    intro i; split_ifs <;> simp_all +decide [ Real.log_div, ne_of_gt, Real.exp_pos ] ;
    rw [ Real.log_div ( by positivity ) ( by exact ne_of_gt ( softmaxProb_pos hn τ x i ) ), log_softmaxProb hn τ x i ] ; ring;
  simp_all +decide [ Finset.sum_ite ];
  rw [ div_le_iff₀' hτ ] at h_gibbs ; rw [ hp.2 ] at h_gibbs ; linarith
