-- Prove2me | solution 1 for bernoulli_pair_decoupling_spectral_tail_bound_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-24T01:59:15.278229+00:00
-- url     : https://prove2.me/submissions/6b1dcfde-d213-417e-8451-a4b8f9a26a2b

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_rademacher
import Definitions.Def_matrix_completion_bernoulli_measure
import Theorems.Thm_dlp_pair_perfiber_sigma_survival_mixed
import Theorems.Thm_dlp_eq7_pair_integration
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 2000000

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 forward decoupling, k=2.
Closing 9aaf089d (bernoulli_pair_decoupling_spectral_tail_bound_offdiag), survival form.

Strategy (tail-complement of the survival statement):
  P_Ω(‖G(Ω,Ω)‖ > 324·Cdec·thr) ≤ 324·P_pair(‖G(Ω₁,Ω₂)‖ > Cdec·thr).
We build the tail interchange `interchange_tail` and complement it.

The tail interchange is delivered by the eq-6→eq-7 route fed by the per-fiber
σ-survival child (db8a020b) + the eq-7 combinator (d618ebb8), connected to the
G-pair tail via the finite pair-swap equidistribution relabel (Sol_9159bae0 toolkit).
-/

namespace Prove9aaf

abbrev Pt (n1 n2 : ℕ) := Finset (Fin n1 × Fin n2)

-- ===========================================================================
-- (0) ELEMENTARY: weights nonneg, weights sum to one (finite Bernoulli measure)
-- ===========================================================================
theorem weight_nonneg {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Ω : Pt n1 n2) : 0 ≤ bernoulliObservationWeight p Ω := by
  unfold bernoulliObservationWeight
  have h1 : (0:ℝ) ≤ 1 - p := by linarith
  positivity

theorem weights_sum_one {n1 n2 : ℕ} (p : ℝ) :
    ∑ Ω : Pt n1 n2, bernoulliObservationWeight p Ω = 1 := by
  unfold bernoulliObservationWeight
  rw [Fintype.sum_pow_mul_eq_add_pow (Fin n1 × Fin n2) p (1 - p)]
  simp

-- ===========================================================================
-- (1) COMPLEMENT BRIDGES: event prob + complement prob = 1 (single and pair)
-- ===========================================================================
theorem event_prob_add_compl {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Prop) :
    bernoulliEventProb p E + bernoulliEventProb p (fun Ω => ¬ E Ω) = 1 := by
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib]
  conv_rhs => rw [← weights_sum_one (n1 := n1) (n2 := n2) p]
  apply Finset.sum_congr rfl
  intro Ω _
  by_cases h : E Ω <;> simp [h]

theorem pair_event_prob_add_compl {n1 n2 : ℕ} (p : ℝ)
    (E : Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliPairEventProb p E + bernoulliPairEventProb p (fun Ω₁ Ω₂ => ¬ E Ω₁ Ω₂) = 1 := by
  unfold bernoulliPairEventProb
  have hone : (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
      bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂) = 1 := by
    rw [← weights_sum_one (n1 := n1) (n2 := n2) p]
    apply Finset.sum_congr rfl; intro Ω₁ _
    rw [← Finset.mul_sum, weights_sum_one, mul_one]
  conv_rhs => rw [← hone]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Ω₂ _
  by_cases h : E Ω₁ Ω₂ <;>
    simp only [h, not_true, not_false_iff, if_true, if_false, mul_one, mul_zero, add_zero, zero_add]

-- ===========================================================================
-- (2) SWAP TOOLKIT (de la Peña σ-selection on the finite powerset; from Sol_9159bae0)
-- swapL/swapR eps (Ω₁,Ω₂) = the σ-selected copies Z^(1)_σ, Z^(2)_σ with eps = {σ=+1}.
-- ===========================================================================
def swapL {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) : Pt n1 n2 :=
  (q.1 \ epsᶜ) ∪ (q.2 ∩ epsᶜ)
def swapR {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) : Pt n1 n2 :=
  (q.2 \ epsᶜ) ∪ (q.1 ∩ epsᶜ)

theorem swap_invol {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) :
    (swapL eps (swapL eps q, swapR eps q), swapR eps (swapL eps q, swapR eps q)) = q := by
  have hL : swapL eps (swapL eps q, swapR eps q) = q.1 := by
    ext a; simp only [swapL, swapR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_compl]; by_cases he : a ∈ eps <;> simp [he]
  have hR : swapR eps (swapL eps q, swapR eps q) = q.2 := by
    ext a; simp only [swapL, swapR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_compl]; by_cases he : a ∈ eps <;> simp [he]
  rw [Prod.ext_iff]; exact ⟨hL, hR⟩

theorem wprod {n1 n2 : ℕ} (p : ℝ) (eps Ω Ω' : Pt n1 n2) :
    bernoulliObservationWeight p ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)) *
        bernoulliObservationWeight p ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ))
      = bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' := by
  have d1 : Disjoint (Ω \ epsᶜ) (Ω' ∩ epsᶜ) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha hb; exact ha.2 hb.2
  have d2 : Disjoint (Ω' \ epsᶜ) (Ω ∩ epsᶜ) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha hb; exact ha.2 hb.2
  have e1 : (Ω \ epsᶜ).card + (Ω ∩ epsᶜ).card = Ω.card :=
    Finset.card_sdiff_add_card_inter Ω epsᶜ
  have e2 : (Ω' \ epsᶜ).card + (Ω' ∩ epsᶜ).card = Ω'.card :=
    Finset.card_sdiff_add_card_inter Ω' epsᶜ
  have hcard : ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)).card + ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)).card
      = Ω.card + Ω'.card := by
    rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2]; omega
  unfold bernoulliObservationWeight
  set N := Fintype.card (Fin n1 × Fin n2) with hN
  set a := ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)).card with ha
  set b := ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)).card with hb
  have hcΩ : Ω.card ≤ N := Finset.card_le_univ _
  have hcΩ' : Ω'.card ≤ N := Finset.card_le_univ _
  have hca : a ≤ N := ha ▸ Finset.card_le_univ _
  have hcb : b ≤ N := hb ▸ Finset.card_le_univ _
  rw [show p ^ a * (1-p) ^ (N - a) * (p ^ b * (1-p) ^ (N - b))
        = p ^ (a + b) * (1-p) ^ ((N - a) + (N - b)) from by rw [pow_add, pow_add]; ring,
    show p ^ Ω.card * (1-p) ^ (N - Ω.card) * (p ^ Ω'.card * (1-p) ^ (N - Ω'.card))
        = p ^ (Ω.card + Ω'.card) * (1-p) ^ ((N - Ω.card) + (N - Ω'.card)) from by
          rw [pow_add, pow_add]; ring]
  rw [hcard]; congr 2; omega

-- generic pair-event relabel under the swap (the EQUIDISTRIBUTION identity).
theorem pair_swap_relabel {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2)
    (event : Pt n1 n2 → Pt n1 n2 → Prop) :
    (∑ Ω : Pt n1 n2, ∑ Ω' : Pt n1 n2,
        bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
          (if event (swapL eps (Ω, Ω')) (swapR eps (Ω, Ω')) then (1:ℝ) else 0))
      = ∑ Ω : Pt n1 n2, ∑ Ω' : Pt n1 n2,
          bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
            (if event Ω Ω' then (1:ℝ) else 0) := by
  rw [← Finset.sum_product', ← Finset.sum_product']
  apply Finset.sum_nbij' (fun z => (swapL eps z, swapR eps z)) (fun z => (swapL eps z, swapR eps z))
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact swap_invol eps z
  · intro z _; exact swap_invol eps z
  · intro z _
    simp only []
    have hw : bernoulliObservationWeight p (swapL eps z) * bernoulliObservationWeight p (swapR eps z)
        = bernoulliObservationWeight p z.1 * bernoulliObservationWeight p z.2 := by
      simp only [swapL, swapR]; exact wprod p eps z.1 z.2
    rw [hw]

-- ===========================================================================
-- (3) STEP-3 BRIDGE: swapL/swapR select the σ-fiber copies at the indicator level,
-- and their cross product is a degree-≤2 rademacherSign chaos (= Tn2 + mixed chaos).
-- ===========================================================================
theorem cI_swapL {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2) (Ω₁ Ω₂ : Pt n1 n2)
    (w : Fin n1 × Fin n2) :
    centeredIndicator (swapL eps (Ω₁, Ω₂)) p w.1 w.2
      = if w ∈ eps then centeredIndicator Ω₁ p w.1 w.2 else centeredIndicator Ω₂ p w.1 w.2 := by
  unfold centeredIndicator swapL
  have h : (w.1, w.2) = w := rfl; rw [h]
  by_cases he : w ∈ eps <;> by_cases h1 : w ∈ Ω₁ <;> by_cases h2 : w ∈ Ω₂ <;>
    simp [he, h1, h2, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]

theorem cI_swapR {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2) (Ω₁ Ω₂ : Pt n1 n2)
    (w : Fin n1 × Fin n2) :
    centeredIndicator (swapR eps (Ω₁, Ω₂)) p w.1 w.2
      = if w ∈ eps then centeredIndicator Ω₂ p w.1 w.2 else centeredIndicator Ω₁ p w.1 w.2 := by
  unfold centeredIndicator swapR
  have h : (w.1, w.2) = w := rfl; rw [h]
  by_cases he : w ∈ eps <;> by_cases h1 : w ∈ Ω₁ <;> by_cases h2 : w ∈ Ω₂ <;>
    simp [he, h1, h2, Finset.mem_union, Finset.mem_inter, Finset.mem_compl]

-- the cross-product mixed split (verified: const + linear σ - linear σ - bilinear σσ).
theorem cross_product_mixed {n1 n2 : ℕ} (p : ℝ) (eps : Pt n1 n2) (Ω₁ Ω₂ : Pt n1 n2)
    (w1 w2 : Fin n1 × Fin n2) :
    centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
        * centeredIndicator (swapR eps (Ω₁, Ω₂)) p w2.1 w2.2
      = (1/4) * (centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
              * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
        + (1/4) * rademacherSign eps w1.1 w1.2
            * (centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)
        - (1/4) * rademacherSign eps w2.1 w2.2
            * (centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)
        - (1/4) * rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2
            * (centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2) := by
  rw [cI_swapL, cI_swapR]
  unfold rademacherSign
  have h1 : (w1.1, w1.2) = w1 := rfl
  have h2 : (w2.1, w2.2) = w2 := rfl
  rw [h1, h2]
  set A1 := centeredIndicator Ω₁ p w1.1 w1.2
  set B1 := centeredIndicator Ω₂ p w1.1 w1.2
  set A2 := centeredIndicator Ω₁ p w2.1 w2.2
  set B2 := centeredIndicator Ω₂ p w2.1 w2.2
  by_cases he1 : w1 ∈ eps <;> by_cases he2 : w2 ∈ eps <;>
    simp only [he1, he2, if_true, if_false] <;> ring

-- ===========================================================================
-- (4) THE KEY MATRIX IDENTITY: 4 • G(swapL, swapR) = Tn2C + mixedChaos,
-- where G uses the off-diag representation with coefficient family `a`.
-- This is the de la Peña eq-4 σ-randomization at the matrix/spectralNorm level.
-- ===========================================================================

-- the off-diagonal decoupled statistic built from `a` (matches 9aaf089d's G).
noncomputable def Goff {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) : RealMatrix n1 n2 :=
  ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
    (if w1 = w2 then (0 : RealMatrix n1 n2)
     else (centeredIndicator Ω₁ p w1.1 w1.2 * centeredIndicator Ω₂ p w2.1 w2.2) • a w1 w2)

-- the four-corner Tn2 statistic = sum of the four corners (Goff at (Ωi,Ωj)).
noncomputable def Tn2 {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) : RealMatrix n1 n2 :=
  Goff a p Ω₁ Ω₁ + Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁ + Goff a p Ω₂ Ω₂

-- the linear coefficient (b) and bilinear coefficient (a') of the mixed σ-chaos.
noncomputable def bCoef {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (w : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  (∑ w2 : Fin n1 × Fin n2, (if w = w2 then (0:RealMatrix n1 n2)
      else ((centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
            * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w w2))
  - (∑ w1 : Fin n1 × Fin n2, (if w1 = w then (0:RealMatrix n1 n2)
      else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
            * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) • a w1 w))

noncomputable def aCoef {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) (w1 w2 : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  (- ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
       * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2))) • a w1 w2

-- Tn2 = the four-corner sum, written as a single off-diagonal double sum with the
-- (A1+B1)(A2+B2) const coefficient (= sum of the four corner coefficients).
theorem Tn2_eq_const_sum {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    Tn2 a p Ω₁ Ω₂ = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
      (if w1 = w2 then (0:RealMatrix n1 n2)
       else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
             * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w1 w2) := by
  unfold Tn2 Goff
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    rw [← add_smul, ← add_smul, ← add_smul]
    congr 1
    ring

-- THE KEY MATRIX IDENTITY (de la Peña eq-4 σ-randomization at the matrix level):
-- 4 • Goff(swapL eps (Ω₁,Ω₂), swapR eps (Ω₁,Ω₂))
--   = Tn2 a p Ω₁ Ω₂ + Σ_w σ_w • bCoef w + Σ_{w1≠w2} σ_{w1}σ_{w2} • aCoef w1 w2.

-- LHS = canonical sum of 4*crossproduct (push 4• inside, smul_smul termwise)
theorem four_Goff_LHS_eq_canon {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (4 : ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂))
      = ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0 : RealMatrix n1 n2)
           else (4 * (centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
                 * centeredIndicator (swapR eps (Ω₁, Ω₂)) p w2.1 w2.2)) • a w1 w2) := by
  unfold Goff
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w1 _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    rw [smul_smul]

-- The canonical sum splits into 4 double sums via cross_product_mixed.
theorem four_Goff_canon_split {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
        (if w1 = w2 then (0 : RealMatrix n1 n2)
         else (4 * (centeredIndicator (swapL eps (Ω₁, Ω₂)) p w1.1 w1.2
               * centeredIndicator (swapR eps (Ω₁, Ω₂)) p w2.1 w2.2)) • a w1 w2))
      = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
          (if w1 = w2 then (0:RealMatrix n1 n2)
           else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2))) • a w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (- (rademacherSign eps w2.1 w2.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)))) • a w1 w2))
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (- (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)))) • a w1 w2)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    rw [cross_product_mixed]
    rw [← add_smul, ← add_smul, ← add_smul]
    congr 1
    ring

-- Term1 (σ_{w1} linear) = ∑_w σ_w • (first bCoef sum)
theorem four_Goff_Term1_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2))) • a w1 w2))
      = ∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 •
          (∑ w2 : Fin n1 × Fin n2, (if w = w2 then (0:RealMatrix n1 n2)
            else ((centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w w2)) := by
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w = w2
  · simp [h]
  · simp only [h, if_false]
    rw [smul_smul]

-- Term2 (σ_{w2} linear) = - ∑_w σ_w • (second bCoef sum)
theorem four_Goff_Term2_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (- (rademacherSign eps w2.1 w2.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)))) • a w1 w2))
      = - ∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 •
          (∑ w1 : Fin n1 × Fin n2, (if w1 = w then (0:RealMatrix n1 n2)
            else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) • a w1 w)) := by
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro w1 _
  by_cases h : w1 = w
  · simp [h]
  · simp only [h, if_false]
    rw [smul_smul, ← neg_smul]

-- Term3 (bilinear) = the bilinear RHS via aCoef
theorem four_Goff_Term3_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0:RealMatrix n1 n2)
             else (- (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2 *
               ((centeredIndicator Ω₁ p w1.1 w1.2 - centeredIndicator Ω₂ p w1.1 w1.2)
                 * (centeredIndicator Ω₁ p w2.1 w2.2 - centeredIndicator Ω₂ p w2.1 w2.2)))) • a w1 w2))
      = (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef a p Ω₁ Ω₂ w1 w2)) := by
  apply Finset.sum_congr rfl; intro w1 _
  apply Finset.sum_congr rfl; intro w2 _
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, if_false]
    unfold aCoef
    rw [smul_smul]
    congr 1
    ring

-- ∑_w σ_w • bCoef w = (first sum) + (- second sum), splitting bCoef via smul_sub
theorem four_Goff_linear_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef a p Ω₁ Ω₂ w)
      = (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 •
          (∑ w2 : Fin n1 × Fin n2, (if w = w2 then (0:RealMatrix n1 n2)
            else ((centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)
                  * (centeredIndicator Ω₁ p w2.1 w2.2 + centeredIndicator Ω₂ p w2.1 w2.2)) • a w w2)))
        + (- ∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 •
          (∑ w1 : Fin n1 × Fin n2, (if w1 = w then (0:RealMatrix n1 n2)
            else ((centeredIndicator Ω₁ p w1.1 w1.2 + centeredIndicator Ω₂ p w1.1 w1.2)
                  * (centeredIndicator Ω₁ p w.1 w.2 - centeredIndicator Ω₂ p w.1 w.2)) • a w1 w))) := by
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro w _
  unfold bCoef
  rw [smul_sub]
  abel

theorem four_Goff_swap_eq {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (eps Ω₁ Ω₂ : Pt n1 n2) :
    (4 : ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂))
      = Tn2 a p Ω₁ Ω₂
        + (∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef a p Ω₁ Ω₂ w)
        + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef a p Ω₁ Ω₂ w1 w2)) := by
  rw [four_Goff_LHS_eq_canon, four_Goff_canon_split]
  rw [← Tn2_eq_const_sum]
  rw [four_Goff_Term1_eq, four_Goff_Term2_eq, four_Goff_Term3_eq]
  rw [four_Goff_linear_eq]
  abel

-- ===========================================================================
-- (5) PER-FIBER SURVIVAL ON THE SWAP: ‖Tn2‖ ≤ ‖4•Goff(swapL,swapR)‖ on ≥1/324 of σ.
-- Composes the survival child (db8a020b) with the matrix identity (4).
-- ===========================================================================
theorem survival_on_swap {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2) (p : ℝ)
    (Ω₁ Ω₂ : Pt n1 n2) :
    rademacherExpectation (fun eps =>
      if spectralNorm (Tn2 a p Ω₁ Ω₂)
          ≤ spectralNorm ((4:ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂)))
      then (1:ℝ) else 0) ≥ 1 / 324 := by
  have hsurv := dlp_pair_perfiber_sigma_survival_mixed
    (bCoef a p Ω₁ Ω₂) (aCoef a p Ω₁ Ω₂) (Tn2 a p Ω₁ Ω₂)
  -- rewrite the survival object via the matrix identity (4)
  have hrw : ∀ eps : Pt n1 n2,
      (Tn2 a p Ω₁ Ω₂ +
        ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef a p Ω₁ Ω₂ w)
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef a p Ω₁ Ω₂ w1 w2))))
        = (4:ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂)) := by
    intro eps; rw [four_Goff_swap_eq]; abel
  -- transport the survival expectation along hrw
  have : (fun eps =>
      if spectralNorm (Tn2 a p Ω₁ Ω₂)
          ≤ spectralNorm ((4:ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂)))
      then (1:ℝ) else 0)
    = (fun eps =>
      if spectralNorm (Tn2 a p Ω₁ Ω₂) ≤ spectralNorm (Tn2 a p Ω₁ Ω₂ +
        ((∑ w : Fin n1 × Fin n2, rademacherSign eps w.1 w.2 • bCoef a p Ω₁ Ω₂ w)
          + (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2)
                  • aCoef a p Ω₁ Ω₂ w1 w2))))
      then (1:ℝ) else 0) := by
    funext eps; rw [hrw eps]
  rw [this]; exact hsurv

-- ===========================================================================
-- (6) THE eq-7 INTERCHANGE (Tn2 four-corner side, FULLY PROVED from the bricks):
--   (1/324)·P_pair(t ≤ ‖Tn2 Ω₁ Ω₂‖) ≤ P_pair(t ≤ ‖4·Goff(Ω₁,Ω₂)‖).
-- Composes survival_on_swap + eq-7 combinator (d618ebb8) + pair_swap_relabel (equidist).
-- ===========================================================================
-- ===========================================================================
-- (6) THE eq-7 INTERCHANGE.
-- GENERIC form (norms opaque ⇒ no whnf storm in the Fubini), then a concrete wrapper.
-- Composes survival_on_swap + eq-7 combinator (d618ebb8) + pair_swap_relabel (equidist).
-- ===========================================================================
theorem eq7_interchange_generic {n1 n2 : ℕ}
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ)
    (Tnorm : Pt n1 n2 → Pt n1 n2 → ℝ)
    (Snorm : Pt n1 n2 → Pt n1 n2 → Pt n1 n2 → ℝ)
    (Dnorm : Pt n1 n2 → Pt n1 n2 → ℝ)
    (hsurv : ∀ Ω₁ Ω₂ : Pt n1 n2,
      rademacherExpectation (fun eps => if Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0) ≥ 1/324)
    (hrelabel : ∀ eps : Pt n1 n2,
      (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
      = ∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Dnorm Ω₁ Ω₂ then (1:ℝ) else 0))
    (hrefine : ∀ Ω₁ Ω₂ eps : Pt n1 n2,
      t < Tnorm Ω₁ Ω₂ → Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ → t < Snorm eps Ω₁ Ω₂) :
    (1/324) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Tnorm Ω₁ Ω₂)
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Dnorm Ω₁ Ω₂) := by
  have hstep1 : (1/324) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Tnorm Ω₁ Ω₂)
      ≤ bernoulliPairExpectation p
          (fun Ω₁ Ω₂ => rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
    apply dlp_eq7_pair_integration p hp0 hp1 (1/324) (by norm_num)
    · intro Ω₁ Ω₂
      unfold rademacherExpectation rademacherObservationWeight
      apply Finset.sum_nonneg; intro eps _
      apply mul_nonneg (by positivity); dsimp only; split <;> norm_num
    · intro Ω₁ Ω₂ hgood
      have hmono : rademacherExpectation
            (fun eps => if Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)
          ≤ rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0) := by
        unfold rademacherExpectation rademacherObservationWeight
        apply Finset.sum_le_sum; intro eps _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only
        by_cases hT : Tnorm Ω₁ Ω₂ ≤ Snorm eps Ω₁ Ω₂
        · rw [if_pos hT, if_pos (hrefine Ω₁ Ω₂ eps hgood hT)]
        · rw [if_neg hT]; split <;> norm_num
      exact le_trans (hsurv Ω₁ Ω₂) hmono
  have hstep2 : bernoulliPairExpectation p
          (fun Ω₁ Ω₂ => rademacherExpectation (fun eps => if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
      = bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < Dnorm Ω₁ Ω₂) := by
    unfold bernoulliPairExpectation bernoulliPairEventProb rademacherExpectation
    have hpush : ∀ Ω₁ Ω₂ : Pt n1 n2,
        bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
            (∑ eps : Pt n1 n2, rademacherObservationWeight eps *
              (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))
          = ∑ eps : Pt n1 n2, rademacherObservationWeight eps *
              (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
      intro Ω₁ Ω₂; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro eps _; ring
    simp only [hpush]
    rw [Finset.sum_congr rfl (fun Ω₁ _ => Finset.sum_comm (γ := Pt n1 n2)
      (f := fun Ω₂ eps => rademacherObservationWeight eps *
        (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
          (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0))))]
    rw [Finset.sum_comm (γ := Pt n1 n2)]
    have hslice : ∀ eps : Pt n1 n2,
        (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
          rademacherObservationWeight eps *
            (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
              (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)))
          = rademacherObservationWeight eps *
              (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
                bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                  (if t < Dnorm Ω₁ Ω₂ then (1:ℝ) else 0)) := by
      intro eps
      have hfac : (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
            rademacherObservationWeight eps *
              (bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)))
          = rademacherObservationWeight eps *
              (∑ Ω₁ : Pt n1 n2, ∑ Ω₂ : Pt n1 n2,
                bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ *
                  (if t < Snorm eps Ω₁ Ω₂ then (1:ℝ) else 0)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Ω₁ _; rw [Finset.mul_sum]
      rw [hfac, hrelabel eps]
    rw [Finset.sum_congr rfl (fun eps _ => hslice eps)]
    rw [← Finset.sum_mul]
    have hradsum : ∑ eps : Pt n1 n2, rademacherObservationWeight eps = 1 := by
      unfold rademacherObservationWeight
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, ← mul_pow]
      norm_num
    rw [hradsum, one_mul]
  rw [← hstep2]; exact hstep1

-- concrete instantiation: the Tn2-side interchange for our matrix statistics.
theorem eq7_interchange {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) :
    (1/324) * bernoulliPairEventProb p (fun Ω₁ Ω₂ => t < spectralNorm (Tn2 a p Ω₁ Ω₂))
      ≤ bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => t < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂)) := by
  refine eq7_interchange_generic p hp0 hp1 t
    (fun Ω₁ Ω₂ => spectralNorm (Tn2 a p Ω₁ Ω₂))
    (fun eps Ω₁ Ω₂ => spectralNorm ((4:ℝ) • Goff a p (swapL eps (Ω₁, Ω₂)) (swapR eps (Ω₁, Ω₂))))
    (fun Ω₁ Ω₂ => spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂))
    (fun Ω₁ Ω₂ => survival_on_swap a p Ω₁ Ω₂)
    ?_
    (fun Ω₁ Ω₂ eps h1 h2 => lt_of_lt_of_le h1 h2)
  -- hrelabel: pair_swap_relabel with event = (t < ‖4•Goff‖); Snorm = Dnorm∘swap by rfl.
  intro eps
  exact pair_swap_relabel p eps (fun Ω₁ Ω₂ => t < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂))

-- spectralNorm is 1-homogeneous: ‖c • X‖ = |c|·‖X‖.
theorem spectralNorm_smul {n1 n2 : ℕ} (c : ℝ) (X : RealMatrix n1 n2) :
    spectralNorm (c • X) = |c| * spectralNorm X := by
  unfold spectralNorm
  rw [map_smul, map_smul, norm_smul]; simp [Real.norm_eq_abs]

-- spectralNorm triangle inequality.
theorem spectralNorm_tri {n1 n2 : ℕ} (X Y : RealMatrix n1 n2) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm; rw [map_add, map_add]; exact norm_add_le _ _

-- spectralNorm sub-triangle inequality.
theorem spectralNorm_sub_tri {n1 n2 : ℕ} (X Y : RealMatrix n1 n2) :
    spectralNorm (X - Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm; rw [map_sub, map_sub]; exact norm_sub_le _ _

-- monotonicity of bernoulliPairEventProb in the event (under nonneg weights).
theorem pair_event_prob_mono {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E F : Pt n1 n2 → Pt n1 n2 → Prop) (hEF : ∀ Ω₁ Ω₂, E Ω₁ Ω₂ → F Ω₁ Ω₂) :
    bernoulliPairEventProb p E ≤ bernoulliPairEventProb p F := by
  unfold bernoulliPairEventProb
  apply Finset.sum_le_sum; intro Ω₁ _
  apply Finset.sum_le_sum; intro Ω₂ _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg hp0 hp1 _) (weight_nonneg hp0 hp1 _))
  by_cases h : E Ω₁ Ω₂
  · rw [if_pos h, if_pos (hEF Ω₁ Ω₂ h)]
  · rw [if_neg h]; split <;> norm_num

-- union bound on pair event prob: E → F ∨ G pointwise ⇒ P(E) ≤ P(F)+P(G).
theorem pair_union_bound {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E F G : Pt n1 n2 → Pt n1 n2 → Prop) (hEFG : ∀ Ω₁ Ω₂, E Ω₁ Ω₂ → F Ω₁ Ω₂ ∨ G Ω₁ Ω₂) :
    bernoulliPairEventProb p E ≤ bernoulliPairEventProb p F + bernoulliPairEventProb p G := by
  unfold bernoulliPairEventProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro Ω₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro Ω₂ _
  have hw : 0 ≤ bernoulliObservationWeight p Ω₁ * bernoulliObservationWeight p Ω₂ :=
    mul_nonneg (weight_nonneg hp0 hp1 _) (weight_nonneg hp0 hp1 _)
  by_cases hE : E Ω₁ Ω₂
  · rcases hEFG Ω₁ Ω₂ hE with hF | hG
    · rw [if_pos hE, if_pos hF]
      have : (0:ℝ) ≤ (if G Ω₁ Ω₂ then (1:ℝ) else 0) := by split <;> norm_num
      nlinarith [hw]
    · rw [if_pos hE, if_pos hG]
      have : (0:ℝ) ≤ (if F Ω₁ Ω₂ then (1:ℝ) else 0) := by split <;> norm_num
      nlinarith [hw]
  · rw [if_neg hE]
    have h1 : (0:ℝ) ≤ (if F Ω₁ Ω₂ then (1:ℝ) else 0) := by split <;> norm_num
    have h2 : (0:ℝ) ≤ (if G Ω₁ Ω₂ then (1:ℝ) else 0) := by split <;> norm_num
    nlinarith [hw]

-- swap Ω₁↔Ω₂ in a pair event prob (the i.i.d. exchangeability, via Finset.sum_comm).
theorem pair_swap_args {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => E Ω₂ Ω₁) = bernoulliPairEventProb p E := by
  unfold bernoulliPairEventProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω₁ _; apply Finset.sum_congr rfl; intro Ω₂ _
  ring_nf

-- ===========================================================================
-- (6b) de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) LEMMA 1, 3-copy
-- symmetrization, spectralNorm-native on the finite Bernoulli powerset model:
--   P_Ω(s < ‖X Ω‖) ≤ 3·P_pair(2s/3 < ‖X Ω₁ + X Ω₂‖)   for ANY per-block X.
-- ===========================================================================
namespace L1Diag

theorem spectralNorm_two_smul {n1 n2 : ℕ} (X : RealMatrix n1 n2) :
    spectralNorm ((2:ℝ) • X) = 2 * spectralNorm X := by
  rw [spectralNorm_smul]; norm_num

theorem single_eq_triple {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Prop) :
    bernoulliEventProb p (fun Ω => E Ω)
      = bernoulliTripleEventProb p (fun Ω _ _ => E Ω) := by
  classical
  unfold bernoulliEventProb bernoulliTripleEventProb
  apply Finset.sum_congr rfl; intro Ω1 _
  have h3 : ∀ Ω2 : Pt n1 n2,
      (∑ Ω3 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
          bernoulliObservationWeight p Ω3 * (if E Ω1 then 1 else 0))
        = bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
            (if E Ω1 then 1 else 0) := by
    intro Ω2
    rw [← Finset.sum_mul]
    have : ∑ Ω3 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
          bernoulliObservationWeight p Ω3
        = bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 := by
      rw [← Finset.mul_sum, weights_sum_one, mul_one]
    rw [this]
  rw [Finset.sum_congr rfl (fun Ω2 _ => h3 Ω2)]
  have : ∑ Ω2 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
        (if E Ω1 then 1 else 0)
      = bernoulliObservationWeight p Ω1 * (if E Ω1 then 1 else 0) := by
    rw [Finset.sum_congr rfl (fun Ω2 _ => by ring :
      ∀ Ω2 ∈ (Finset.univ : Finset (Pt n1 n2)),
        bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
          (if E Ω1 then 1 else 0)
        = bernoulliObservationWeight p Ω2 *
          (bernoulliObservationWeight p Ω1 * (if E Ω1 then 1 else 0)))]
    rw [← Finset.sum_mul, weights_sum_one, one_mul]
  rw [this]
  by_cases h : E Ω1 <;> simp [h]

theorem pair_eq_triple {n1 n2 : ℕ} (p : ℝ) (E : Pt n1 n2 → Pt n1 n2 → Prop) :
    bernoulliPairEventProb p (fun Ω1 Ω2 => E Ω1 Ω2)
      = bernoulliTripleEventProb p (fun Ω1 Ω2 _ => E Ω1 Ω2) := by
  classical
  unfold bernoulliPairEventProb bernoulliTripleEventProb
  apply Finset.sum_congr rfl; intro Ω1 _
  apply Finset.sum_congr rfl; intro Ω2 _
  rw [← Finset.sum_mul]
  have : ∑ Ω3 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
        bernoulliObservationWeight p Ω3
      = bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 := by
    rw [← Finset.mul_sum, weights_sum_one, mul_one]
  rw [this]

theorem htri {n1 n2 : ℕ} (X1 X2 X3 : RealMatrix n1 n2) (s : ℝ)
    (hs : s < spectralNorm X1) :
    (2*s/3 < spectralNorm (X1 + X2)) ∨ (2*s/3 < spectralNorm (X1 + X3)) ∨
      (2*s/3 < spectralNorm (X2 + X3)) := by
  have hid : (2:ℝ) • X1 = (X1 + X2) + (X1 + X3) - (X2 + X3) := by rw [two_smul]; abel
  have h2 : 2 * spectralNorm X1 = spectralNorm ((2:ℝ) • X1) := (spectralNorm_two_smul X1).symm
  have htria : spectralNorm ((X1 + X2) + (X1 + X3) - (X2 + X3))
      ≤ spectralNorm (X1 + X2) + spectralNorm (X1 + X3) + spectralNorm (X2 + X3) := by
    have e1 : (X1 + X2) + (X1 + X3) - (X2 + X3)
        = ((X1 + X2) + (X1 + X3)) + (-(1:ℝ)) • (X2 + X3) := by rw [neg_one_smul]; abel
    rw [e1]
    refine le_trans (spectralNorm_tri _ _) ?_
    have hneg : spectralNorm ((-(1:ℝ)) • (X2 + X3)) = spectralNorm (X2 + X3) := by
      rw [spectralNorm_smul]; norm_num
    rw [hneg]
    have := spectralNorm_tri (X1 + X2) (X1 + X3)
    linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have hsum : spectralNorm (X1 + X2) + spectralNorm (X1 + X3) + spectralNorm (X2 + X3)
      ≤ 2*s := by linarith
  rw [hid] at h2
  have : 2 * spectralNorm X1 ≤ 2*s := le_trans (h2.le.trans htria) hsum
  linarith

theorem indicator_union {P Q1 Q2 Q3 : Prop} [Decidable P] [Decidable Q1]
    [Decidable Q2] [Decidable Q3] (h : P → Q1 ∨ Q2 ∨ Q3) :
    (if P then (1:ℝ) else 0)
      ≤ (if Q1 then 1 else 0) + (if Q2 then 1 else 0) + (if Q3 then 1 else 0) := by
  by_cases hP : P
  · simp only [hP, if_true]
    rcases h hP with hq | hq | hq
    · simp only [hq, if_true]; by_cases Q2 <;> by_cases Q3 <;> simp_all <;> norm_num
    · simp only [hq, if_true]; by_cases Q1 <;> by_cases Q3 <;> simp_all <;> norm_num
    · simp only [hq, if_true]; by_cases Q1 <;> by_cases Q2 <;> simp_all <;> norm_num
  · simp only [hP, if_false]; positivity

theorem triple_union_bound {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliTripleEventProb p (fun Ω1 _ _ => s < spectralNorm (X Ω1))
      ≤ bernoulliTripleEventProb p (fun Ω1 Ω2 _ => 2*s/3 < spectralNorm (X Ω1 + X Ω2))
        + bernoulliTripleEventProb p (fun Ω1 _ Ω3 => 2*s/3 < spectralNorm (X Ω1 + X Ω3))
        + bernoulliTripleEventProb p (fun _ Ω2 Ω3 => 2*s/3 < spectralNorm (X Ω2 + X Ω3)) := by
  classical
  unfold bernoulliTripleEventProb
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro Ω1 _
  apply Finset.sum_le_sum; intro Ω2 _
  apply Finset.sum_le_sum; intro Ω3 _
  set w := bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
    bernoulliObservationWeight p Ω3 with hw
  have hwnn : 0 ≤ w := by
    rw [hw]
    have h1 := weight_nonneg hp0 hp1 Ω1
    have h2 := weight_nonneg hp0 hp1 Ω2
    have h3 := weight_nonneg hp0 hp1 Ω3
    positivity
  have hind := indicator_union (P := s < spectralNorm (X Ω1))
    (Q1 := 2*s/3 < spectralNorm (X Ω1 + X Ω2))
    (Q2 := 2*s/3 < spectralNorm (X Ω1 + X Ω3))
    (Q3 := 2*s/3 < spectralNorm (X Ω2 + X Ω3))
    (fun h => htri (X Ω1) (X Ω2) (X Ω3) s h)
  have := mul_le_mul_of_nonneg_left hind hwnn
  calc w * (if s < spectralNorm (X Ω1) then (1:ℝ) else 0)
      ≤ w * ((if 2*s/3 < spectralNorm (X Ω1 + X Ω2) then 1 else 0)
            + (if 2*s/3 < spectralNorm (X Ω1 + X Ω3) then 1 else 0)
            + (if 2*s/3 < spectralNorm (X Ω2 + X Ω3) then 1 else 0)) := this
    _ = w * (if 2*s/3 < spectralNorm (X Ω1 + X Ω2) then 1 else 0)
          + w * (if 2*s/3 < spectralNorm (X Ω1 + X Ω3) then 1 else 0)
          + w * (if 2*s/3 < spectralNorm (X Ω2 + X Ω3) then 1 else 0) := by ring

theorem pairProb {n1 n2 : ℕ} (p : ℝ) (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliPairEventProb p (fun Ω1 Ω2 => 2*s/3 < spectralNorm (X Ω1 + X Ω2))
      = bernoulliTripleEventProb p (fun Ω1 Ω2 _ => 2*s/3 < spectralNorm (X Ω1 + X Ω2)) :=
  pair_eq_triple p (fun Ω1 Ω2 => 2*s/3 < spectralNorm (X Ω1 + X Ω2))

theorem E13_eq_pair {n1 n2 : ℕ} (p : ℝ) (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliTripleEventProb p (fun Ω1 _ Ω3 => 2*s/3 < spectralNorm (X Ω1 + X Ω3))
      = bernoulliPairEventProb p (fun Ω1 Ω2 => 2*s/3 < spectralNorm (X Ω1 + X Ω2)) := by
  classical
  rw [pairProb]
  unfold bernoulliTripleEventProb
  apply Finset.sum_congr rfl; intro Ω1 _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω3 _
  apply Finset.sum_congr rfl; intro Ω2 _
  ring

theorem E23_eq_pair {n1 n2 : ℕ} (p : ℝ) (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliTripleEventProb p (fun _ Ω2 Ω3 => 2*s/3 < spectralNorm (X Ω2 + X Ω3))
      = bernoulliPairEventProb p (fun Ω1 Ω2 => 2*s/3 < spectralNorm (X Ω1 + X Ω2)) := by
  classical
  unfold bernoulliTripleEventProb bernoulliPairEventProb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω2 _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro Ω3 _
  rw [← Finset.sum_mul]
  have hsum : ∑ Ω1 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
        bernoulliObservationWeight p Ω3
      = bernoulliObservationWeight p Ω2 * bernoulliObservationWeight p Ω3 := by
    have : ∀ Ω1 : Pt n1 n2, bernoulliObservationWeight p Ω1 * bernoulliObservationWeight p Ω2 *
          bernoulliObservationWeight p Ω3
        = bernoulliObservationWeight p Ω1 *
          (bernoulliObservationWeight p Ω2 * bernoulliObservationWeight p Ω3) := fun Ω1 => by ring
    rw [Finset.sum_congr rfl (fun Ω1 _ => this Ω1), ← Finset.sum_mul, weights_sum_one, one_mul]
  rw [hsum]

theorem lemma1_diag_3copy {n1 n2 : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Pt n1 n2 → RealMatrix n1 n2) (s : ℝ) :
    bernoulliEventProb p (fun Ω => s < spectralNorm (X Ω))
      ≤ 3 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (X Ω₁ + X Ω₂)) := by
  rw [single_eq_triple p (fun Ω => s < spectralNorm (X Ω))]
  refine le_trans (triple_union_bound p hp0 hp1 X s) ?_
  rw [← pairProb p X s, E13_eq_pair p X s, E23_eq_pair p X s]
  exact le_of_eq (by ring)

end L1Diag
-- ===========================================================================
-- (7) THE FAITHFUL de la Peña Lemma 1 / eq-5 (k=2): diagonal → TWO-DIAGONAL-CORNER.
-- THE PRECISE REMAINING RESIDUAL.  de la Peña–Montgomery-Smith 1995 (arXiv:math/
-- 9309211) §4 eqs (4)-(5) p.811: the single-sample diagonal U-statistic Goff(Ω,Ω)
-- desymmetrizes to the TWO-DIAGONAL-CORNER sum Goff(Ω₁,Ω₁)+Goff(Ω₂,Ω₂) (the
-- "X+Y" of the 3-copy triangle Lemma 1), constant 3, threshold 2/3.  This is the
-- spectralNorm-valued 3-copy symmetrization on the powerset model.  It is NOT
-- among the listed children (scalar a49de65e has the wrong norming direction;
-- abstract d1b80fe6 cannot instantiate at V = RealMatrix — no NormedAddCommGroup/
-- MeasurableSpace instance).  The cross-term and Tn2 routing BELOW is sorry-free.
-- ===========================================================================
theorem lemma1_diag_to_two_corner {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliEventProb p (fun Ω => s < spectralNorm (Goff a p Ω Ω))
      ≤ 3 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂)) := by
  exact L1Diag.lemma1_diag_3copy p hp0 hp1 (fun Ω => Goff a p Ω Ω) s

-- ===========================================================================
-- (8) TWO-CORNER → TARGET routing (FULLY PROVED): the two-diagonal-corner pair
-- tail is bounded by the decoupled Goff(Ω₁,Ω₂) tail, via the triangle splits
-- two-corner = Tn2 − cross, cross = Goff(Ω₁,Ω₂)+Goff(Ω₂,Ω₁), + eq7_interchange.
-- ===========================================================================
theorem two_corner_to_target {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliPairEventProb p (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂))
      ≤ 326 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
  -- two-corner = Tn2 − cross  ⇒  ‖two-corner‖ ≤ ‖Tn2‖ + ‖cross‖, cross = G12+G21.
  -- {2s/3 < ‖two-corner‖} ⊆ {s/3 < ‖Tn2‖} ∪ {s/3 < ‖cross‖}.
  have htc_eq : ∀ Ω₁ Ω₂ : Pt n1 n2,
      Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂
        = Tn2 a p Ω₁ Ω₂ - (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁) := by
    intro Ω₁ Ω₂; unfold Tn2; abel
  -- Step 1: union bound (two-corner) ⊆ (Tn2) ∪ (cross).
  have hstep1 : bernoulliPairEventProb p
        (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂))
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Tn2 a p Ω₁ Ω₂))
        + bernoulliPairEventProb p
            (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁)) := by
    apply pair_union_bound hp0 hp1
    intro Ω₁ Ω₂ htc
    rw [htc_eq] at htc
    have htri := spectralNorm_sub_tri (Tn2 a p Ω₁ Ω₂) (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁)
    -- 2s/3 < ‖Tn2‖ + ‖cross‖ ⇒ s/3 < ‖Tn2‖ ∨ s/3 < ‖cross‖
    by_contra hcon; push_neg at hcon
    exact absurd (lt_of_lt_of_le htc htri) (by linarith [hcon.1, hcon.2])
  -- Step 2: cross = G12+G21 ⊆ (G12) ∪ (G21); union bound + swap.
  have hstep2 : bernoulliPairEventProb p
        (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁))
      ≤ 2 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    have hub := pair_union_bound hp0 hp1
      (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁))
      (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂))
      (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₂ Ω₁))
      (by
        intro Ω₁ Ω₂ hc
        have htri := spectralNorm_tri (Goff a p Ω₁ Ω₂) (Goff a p Ω₂ Ω₁)
        by_contra hcon; push_neg at hcon
        exact absurd (lt_of_lt_of_le hc htri) (by linarith [hcon.1, hcon.2]))
    -- the G21 term swaps to the G12 term.
    have hswap : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₂ Ω₁))
        = bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂)) :=
      pair_swap_args p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂))
    rw [hswap] at hub; linarith [hub]
  -- Step 3: Tn2 tail → eq7_interchange → 324·P(s/12 < ‖Goff‖).
  have hE7 := eq7_interchange a p hp0 hp1 (s/3)
  have hsmul : ∀ Ω₁ Ω₂ : Pt n1 n2,
      ((s/3) < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂)) ↔ ((s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    intro Ω₁ Ω₂; rw [spectralNorm_smul]
    have h4 : |(4:ℝ)| = 4 := by norm_num
    rw [h4]; constructor <;> intro h <;> linarith
  have hEv : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/3) < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂))
      = bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    unfold bernoulliPairEventProb
    apply Finset.sum_congr rfl; intro Ω₁ _; apply Finset.sum_congr rfl; intro Ω₂ _
    rw [show (if (s/3) < spectralNorm ((4:ℝ) • Goff a p Ω₁ Ω₂) then (1:ℝ) else 0)
        = (if (s/12) < spectralNorm (Goff a p Ω₁ Ω₂) then (1:ℝ) else 0) from by
      by_cases h : (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)
      · rw [if_pos h, if_pos ((hsmul Ω₁ Ω₂).mpr h)]
      · rw [if_neg h, if_neg (fun hc => h ((hsmul Ω₁ Ω₂).mp hc))]]
  rw [hEv] at hE7
  have hTn2 : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Tn2 a p Ω₁ Ω₂))
      ≤ 324 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    nlinarith [hE7]
  -- the cross branch's s/6 tail ≤ s/12 tail (monotone threshold; uses ‖·‖ ≥ 0
  -- so the s<0 case is fine: s/12 < 0 ≤ ‖Goff‖ always).
  have hmono : bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂))
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
    apply pair_event_prob_mono hp0 hp1
    intro Ω₁ Ω₂ h
    have hsn : (0:ℝ) ≤ spectralNorm (Goff a p Ω₁ Ω₂) := by unfold spectralNorm; exact norm_nonneg _
    rcases lt_or_ge s 0 with hs | hs
    · linarith
    · linarith
  -- combine: ≤ 324·P + 2·P ≤ 326·P (at threshold s/12).
  calc bernoulliPairEventProb p (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂))
      ≤ bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Tn2 a p Ω₁ Ω₂))
        + bernoulliPairEventProb p
            (fun Ω₁ Ω₂ => (s/3) < spectralNorm (Goff a p Ω₁ Ω₂ + Goff a p Ω₂ Ω₁)) := hstep1
    _ ≤ 324 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂))
        + 2 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/6) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
        linarith [hTn2, hstep2]
    _ ≤ 326 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
        linarith [hmono]

-- ===========================================================================
-- (8b) THE de la Peña FORWARD TAIL BOUND (diagonal ≤ 978·decoupled, threshold /12).
-- Chains the faithful Lemma 1 (residual) + two_corner_to_target (Proved).
-- ===========================================================================
theorem dlp_forward_tail {n1 n2 : ℕ}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) :
    bernoulliEventProb p (fun Ω => s < spectralNorm (Goff a p Ω Ω))
      ≤ 978 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by
  have hL1 := lemma1_diag_to_two_corner a p hp0 hp1 s
  have hTC := two_corner_to_target a p hp0 hp1 s
  calc bernoulliEventProb p (fun Ω => s < spectralNorm (Goff a p Ω Ω))
      ≤ 3 * bernoulliPairEventProb p
          (fun Ω₁ Ω₂ => (2*s/3) < spectralNorm (Goff a p Ω₁ Ω₁ + Goff a p Ω₂ Ω₂)) := hL1
    _ ≤ 3 * (326 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂))) := by
        apply mul_le_mul_of_nonneg_left hTC (by norm_num)
    _ = 978 * bernoulliPairEventProb p (fun Ω₁ Ω₂ => (s/12) < spectralNorm (Goff a p Ω₁ Ω₂)) := by ring

end Prove9aaf

open Prove9aaf

-- ===========================================================================
-- (9) FINAL THEOREM — 9aaf089d's survival form (K = 12, L = 978), via the
-- complement of dlp_forward_tail.  Modulo the single residual lemma1_diag_to_two_corner.
-- ===========================================================================
theorem solution :
    ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ : ℕ}
        (G : Finset (Fin n₁ × Fin n₂) →
             Finset (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂)
        (p Cdec cdec failureScale thresholdScale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        (∃ a : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) → RealMatrix n₁ n₂,
            ∀ Omega1 Omega2 : Finset (Fin n₁ × Fin n₂),
              G Omega1 Omega2 =
                ∑ w1 : Fin n₁ × Fin n₂, ∑ w2 : Fin n₁ × Fin n₂,
                  (if w1 = w2 then (0 : RealMatrix n₁ n₂)
                   else
                     (centeredIndicator Omega1 p w1.1 w1.2 *
                       centeredIndicator Omega2 p w2.1 w2.2) • a w1 w2)) →
        bernoulliPairEventProb p
            (fun Omega1 Omega2 =>
              spectralNorm (G Omega1 Omega2) ≤ Cdec * thresholdScale) ≥
          1 - cdec * failureScale →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (G Omega Omega) ≤ (K * Cdec) * thresholdScale) ≥
          1 - (L * cdec) * failureScale := by
  refine ⟨12, 978, by norm_num, by norm_num, ?_⟩
  intro n₁ n₂ G p Cdec cdec failureScale thresholdScale hp0 hp1 hCdec hcdec hrep hpair
  obtain ⟨a, ha⟩ := hrep
  -- G = Goff a p (off-diagonal representation).
  have hG : ∀ Ω₁ Ω₂, G Ω₁ Ω₂ = Goff a p Ω₁ Ω₂ := by
    intro Ω₁ Ω₂; rw [ha]; rfl
  -- pair tail (strict complement of hyp): P_pair(Cdec·thr < ‖G‖) ≤ cdec·fail.
  have hpair_tail : bernoulliPairEventProb p
      (fun Ω₁ Ω₂ => Cdec * thresholdScale < spectralNorm (G Ω₁ Ω₂)) ≤ cdec * failureScale := by
    have hc := pair_event_prob_add_compl p
      (fun Ω₁ Ω₂ => spectralNorm (G Ω₁ Ω₂) ≤ Cdec * thresholdScale)
    have heq : bernoulliPairEventProb p
        (fun Ω₁ Ω₂ => ¬ (spectralNorm (G Ω₁ Ω₂) ≤ Cdec * thresholdScale))
      = bernoulliPairEventProb p (fun Ω₁ Ω₂ => Cdec * thresholdScale < spectralNorm (G Ω₁ Ω₂)) := by
      unfold bernoulliPairEventProb
      apply Finset.sum_congr rfl; intro Ω₁ _; apply Finset.sum_congr rfl; intro Ω₂ _
      congr 1; simp only [not_le]
    rw [heq] at hc
    -- hpair : 1 - cdec·fail ≤ P_pair(good);  hc : P_pair(good) + P_pair(strict) = 1.
    have : (1:ℝ) - cdec * failureScale ≤
        bernoulliPairEventProb p (fun Ω₁ Ω₂ => spectralNorm (G Ω₁ Ω₂) ≤ Cdec * thresholdScale) := hpair
    linarith [hc]
  -- forward tail (Goff form) at s = 12·Cdec·thr, threshold s/12 = Cdec·thr:
  have hfwd := dlp_forward_tail a p hp0 hp1 (12 * Cdec * thresholdScale)
  have hs12 : (12 * Cdec * thresholdScale) / 12 = Cdec * thresholdScale := by ring
  rw [hs12] at hfwd
  -- rewrite Goff↔G via hG in hfwd (both diagonal and pair events).
  have hGdiag : ∀ Ω : Pt n₁ n₂, Goff a p Ω Ω = G Ω Ω := fun Ω => (hG Ω Ω).symm
  have hGpair : ∀ Ω₁ Ω₂ : Pt n₁ n₂, Goff a p Ω₁ Ω₂ = G Ω₁ Ω₂ := fun Ω₁ Ω₂ => (hG Ω₁ Ω₂).symm
  simp only [hGdiag, hGpair] at hfwd
  -- hfwd : P_Ω(12Cdec·thr < ‖G(Ω,Ω)‖) ≤ 978·P_pair(Cdec·thr < ‖G‖).
  -- chain with hpair_tail:  ≤ 978·cdec·fail.
  have hdiag_tail : bernoulliEventProb p
      (fun Ω => (12 * Cdec * thresholdScale) < spectralNorm (G Ω Ω)) ≤ (978 * cdec) * failureScale := by
    calc bernoulliEventProb p (fun Ω => (12 * Cdec * thresholdScale) < spectralNorm (G Ω Ω))
        ≤ 978 * bernoulliPairEventProb p
            (fun Ω₁ Ω₂ => Cdec * thresholdScale < spectralNorm (G Ω₁ Ω₂)) := hfwd
      _ ≤ 978 * (cdec * failureScale) := by
          apply mul_le_mul_of_nonneg_left hpair_tail (by norm_num)
      _ = (978 * cdec) * failureScale := by ring
  -- complement back to the survival-form goal.
  rw [ge_iff_le]
  have hcompl := event_prob_add_compl p
    (fun Ω => spectralNorm (G Ω Ω) ≤ (12 * Cdec) * thresholdScale)
  -- relate the complement event to the strict diagonal tail (note 12*Cdec assoc):
  have hcompl_eq : bernoulliEventProb p
      (fun Ω => ¬ (spectralNorm (G Ω Ω) ≤ (12 * Cdec) * thresholdScale))
    = bernoulliEventProb p (fun Ω => (12 * Cdec * thresholdScale) < spectralNorm (G Ω Ω)) := by
    unfold bernoulliEventProb
    apply Finset.sum_congr rfl; intro Ω _
    have hassoc : (12 * Cdec) * thresholdScale = 12 * Cdec * thresholdScale := by ring
    simp only [not_le, hassoc]
  rw [hcompl_eq] at hcompl
  linarith [hcompl, hdiag_tail]

