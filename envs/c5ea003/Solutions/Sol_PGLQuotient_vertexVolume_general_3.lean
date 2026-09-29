-- Prove2me | solution 3 for PGLQuotient.vertexVolume_general
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:18:42.183895+00:00
-- url     : https://prove2.me/submissions/86468033-8711-4a2d-8556-d2f02b64b021

import Mathlib
import Definitions.Def_Algebra_PGLQuotient_TwistedWeight
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Algebra/PGLQuotient/VertexModel.lean ====
/-!
# The standard arithmetic quotient of `PGL_d`: the vertex model

This file sets up an explicit combinatorial model for the vertex set of the standard
non-uniform arithmetic quotient of the affine Bruhat–Tits building of
`PGL_d (F_q((t^{-1})))` by `Γ = PGL_d(F_q[t])`.

By Soulé's theorem the quotient `Γ \ X` is (simplicially) a dominant sector: its vertices are
in bijection with dominant coweights `λ = (λ_0 ≥ λ_1 ≥ ⋯ ≥ λ_{d-1} = 0)`, and the stabiliser
of the vertex `λ` in `GL_d(F_q[t])` is the group of matrices `(a_{ij})` over `F_q[t]` with
`deg a_{ij} ≤ λ_i - λ_j`; equivalently, it is the automorphism group of the vector bundle
`⨁_i O(λ_i)` on `P^1`, i.e. the unit group of the algebra `End = ⨁_{i,j} H^0(O(λ_i - λ_j))`.
Its order is

`|Aut(λ)| = q^{dim End} * ∏_i (1 - q^{-r_i})`,

where `dim End = ∑_{i,j} max (0, λ_i - λ_j + 1)` and `r_i = #{ j ≤ i : λ_j = λ_i }` is the
position of `i` inside its block of equal entries (so that the second factor accounts for the
Levi `∏_b GL_{m_b}(F_q)` of the block composition).  With the Haar measure normalised so that
a maximal compact subgroup has volume `1`, the vertex `λ` carries the mass `1/|Aut(λ)|`
(`GL`-normalisation) resp. `(q-1)/|Aut(λ)|` (`PGL`-normalisation).

Vertices are parametrised here by their *gaps* `g_k = λ_k - λ_{k+1} ∈ ℕ`, `0 ≤ k ≤ d-2`, i.e.
by `Vertex d = Fin (d-1) → ℕ`.

The homothety-invariant normalised lattice-minima height is
`α(λ) = q^{λ_0 - (λ_0 + ⋯ + λ_{d-1})/d}`, which in gap coordinates reads
`log_q α = (∑_k (d-1-k) g_k)/d`.

## Main results of this file

* `sum_lam_sub_eq_pairExp` : the cut-set/double-counting identity
  `∑_{i,j} (λ_i - λ_j) = ∑_k (k+1)(d-1-k) g_k`;
* `vertexWeight_le`, `vertexWeight_ge` : sharp-order two-sided bounds
  `c₁ q^{-P(g)} ≤ 1/|Aut(λ)| ≤ c₂ q^{-P(g)}` with `P(g) = ∑_k (k+1)(d-1-k) g_k`.

These drive all the analytic results (integrability threshold, cusp tail, height zeta
function) in the companion files.
-/

namespace PGLQuotient

open Finset

-- [dropped: platform already declares Vertex]
variable {d : ℕ}

-- [dropped: platform already declares gapAt]
-- [dropped: platform already declares lam]
-- [dropped: platform already declares endDim]
-- [dropped: platform already declares blockRank]
-- [dropped: platform already declares autOrder]
-- [dropped: platform already declares vertexWeight]
-- [dropped: platform already declares heightExp]
-- [dropped: platform already declares resExp]
-- [dropped: platform already declares pairExp]
-- [dropped: platform already declares height]
section Combinatorics

variable (g : Vertex d)

lemma lam_antitone {i j : ℕ} (h : i ≤ j) : lam g j ≤ lam g i := by
  refine Finset.sum_le_sum_of_subset ?_
  intro k hk
  simp only [Finset.mem_Ico] at hk ⊢
  exact ⟨le_trans h hk.1, hk.2⟩

lemma lam_sub {i j : ℕ} (hij : i ≤ j) (hj : j ≤ d - 1) :
    lam g i - lam g j = ∑ k ∈ Finset.Ico i j, gapAt g k := by
  have : lam g i = (∑ k ∈ Finset.Ico i j, gapAt g k) + lam g j := by
    unfold lam
    rw [← Finset.sum_Ico_consecutive _ hij hj]
  omega

/-- Pointwise description of `λ_i - λ_j` as a gap sum with an indicator. -/
lemma lam_sub_indicator {i j : ℕ} (hj : j < d) :
    lam g i - lam g j = ∑ k ∈ range (d - 1), (if i ≤ k ∧ k < j then gapAt g k else 0) := by
  rw [← Finset.sum_filter]
  by_cases hij : i < j
  · have hjd : j ≤ d - 1 := by omega
    rw [lam_sub g hij.le hjd]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  · have h0 : lam g i - lam g j = 0 := by
      have := lam_antitone g (show j ≤ i by omega); omega
    rw [h0]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter] at hk
    omega

/-- The cut-set double-counting identity `∑_{i,j} (λ_i - λ_j) = ∑_k (k+1)(d-1-k) g_k`. -/
lemma sum_lam_sub_eq_pairExp :
    ∑ i ∈ range d, ∑ j ∈ range d, (lam g i - lam g j) = pairExp g := by
  have h1 : ∀ i ∈ range d, ∑ j ∈ range d, (lam g i - lam g j)
      = ∑ j ∈ range d, ∑ k ∈ range (d-1), (if i ≤ k ∧ k < j then gapAt g k else 0) := by
    intro i _
    exact Finset.sum_congr rfl (fun j hj => lam_sub_indicator g (Finset.mem_range.mp hj))
  rw [Finset.sum_congr rfl h1]
  have step1 : ∀ i : ℕ, ∑ j ∈ range d, ∑ k ∈ range (d-1), (if i ≤ k ∧ k < j then gapAt g k else 0)
      = ∑ k ∈ range (d-1), ∑ j ∈ range d, (if i ≤ k ∧ k < j then gapAt g k else 0) :=
    fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i _ => step1 i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkd : k < d - 1 := Finset.mem_range.mp hk
  have inner : ∀ i : ℕ, ∑ j ∈ range d, (if i ≤ k ∧ k < j then gapAt g k else 0)
      = if i ≤ k then (d - 1 - k) * gapAt g k else 0 := by
    intro i
    by_cases hik : i ≤ k
    · simp only [hik, true_and, if_true]
      rw [← Finset.sum_filter]
      have hfil : (range d).filter (fun j => k < j) = Finset.Ico (k+1) d := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [hfil, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      congr 1
      omega
    · simp [hik]
  rw [Finset.sum_congr rfl (fun i _ => inner i), ← Finset.sum_filter]
  have hfil2 : (range d).filter (fun i => i ≤ k) = range (k+1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfil2, Finset.sum_const, Finset.card_range, smul_eq_mul, ← mul_assoc]

/-- The pair exponent splits into the height exponent and the residual exponent. -/
lemma pairExp_eq : pairExp g = heightExp g + resExp g := by
  unfold pairExp heightExp resExp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

lemma pairExp_le_endDim : pairExp g ≤ endDim g := by
  rw [← sum_lam_sub_eq_pairExp]
  unfold endDim
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  omega

lemma endDim_le_pairExp : endDim g ≤ pairExp g + d * d := by
  rw [← sum_lam_sub_eq_pairExp]
  unfold endDim
  calc ∑ i ∈ range d, ∑ j ∈ range d, (lam g i + 1 - lam g j)
      ≤ ∑ i ∈ range d, ∑ j ∈ range d, ((lam g i - lam g j) + 1) := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        omega
    _ = (∑ i ∈ range d, ∑ j ∈ range d, (lam g i - lam g j)) + d * d := by
        simp [Finset.sum_add_distrib, Finset.sum_const]

lemma one_le_blockRank (i : ℕ) : 1 ≤ blockRank g i := by
  unfold blockRank
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  simp

end Combinatorics

section Bounds

variable {q : ℝ} (g : Vertex d)

lemma inv_lt_one_of_one_lt (hq : 1 < q) : q⁻¹ < 1 := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  rw [inv_lt_one_iff₀]
  right; exact hq

lemma blockFactor_le_one (hq : 1 < q) (r : ℕ) : 1 - q⁻¹ ^ r ≤ 1 := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have : (0:ℝ) ≤ q⁻¹ ^ r := pow_nonneg (le_of_lt (inv_pos.mpr hq0)) r
  linarith

lemma blockFactor_ge (hq : 1 < q) {r : ℕ} (hr : 1 ≤ r) : 1 - q⁻¹ ≤ 1 - q⁻¹ ^ r := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have h1 : q⁻¹ ^ r ≤ q⁻¹ ^ 1 :=
    pow_le_pow_of_le_one (le_of_lt (inv_pos.mpr hq0)) (le_of_lt (inv_lt_one_of_one_lt hq)) hr
  simp only [pow_one] at h1
  linarith

lemma one_sub_inv_pos (hq : 1 < q) : 0 < 1 - q⁻¹ := by
  have := inv_lt_one_of_one_lt hq; linarith

lemma prod_blockFactor_le_one (hq : 1 < q) :
    ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) ≤ 1 := by
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => blockFactor_le_one hq _)
  have := blockFactor_ge (q := q) hq (one_le_blockRank g i)
  have := one_sub_inv_pos (q := q) hq
  linarith

lemma prod_blockFactor_ge (hq : 1 < q) :
    (1 - q⁻¹) ^ d ≤ ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) := by
  have h := one_sub_inv_pos (q := q) hq
  calc (1 - q⁻¹) ^ d = ∏ _i ∈ range d, (1 - q⁻¹) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) := by
        refine Finset.prod_le_prod (fun i _ => le_of_lt h)
          (fun i _ => blockFactor_ge hq (one_le_blockRank g i))

lemma prod_blockFactor_pos (hq : 1 < q) :
    0 < ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) :=
  lt_of_lt_of_le (pow_pos (one_sub_inv_pos hq) d) (prod_blockFactor_ge g hq)

lemma autOrder_pos (hq : 1 < q) : 0 < autOrder q g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  exact mul_pos (pow_pos hq0 _) (prod_blockFactor_pos g hq)

lemma vertexWeight_pos (hq : 1 < q) : 0 < vertexWeight q g :=
  inv_pos.mpr (autOrder_pos g hq)

/-- Upper bound for the vertex mass: `1/|Aut| ≤ (1-1/q)^{-d} q^{-P(g)}`. -/
lemma vertexWeight_le (hq : 1 < q) :
    vertexWeight q g ≤ ((1 - q⁻¹) ^ d)⁻¹ * (q ^ pairExp g)⁻¹ := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hlow : (q ^ pairExp g) * (1 - q⁻¹) ^ d ≤ autOrder q g := by
    unfold autOrder
    refine mul_le_mul ?_ (prod_blockFactor_ge g hq) (le_of_lt (pow_pos (one_sub_inv_pos hq) d))
      (le_of_lt (pow_pos hq0 _))
    exact pow_le_pow_right₀ hq.le (pairExp_le_endDim g)
  have hpos : 0 < (q ^ pairExp g) * (1 - q⁻¹) ^ d :=
    mul_pos (pow_pos hq0 _) (pow_pos (one_sub_inv_pos hq) d)
  unfold vertexWeight
  rw [show ((1 - q⁻¹) ^ d)⁻¹ * (q ^ pairExp g)⁻¹ = ((q ^ pairExp g) * (1 - q⁻¹) ^ d)⁻¹ by
    rw [mul_inv]; ring]
  exact inv_anti₀ hpos hlow

/-- Lower bound for the vertex mass: `q^{-d^2} q^{-P(g)} ≤ 1/|Aut|`. -/
lemma vertexWeight_ge (hq : 1 < q) :
    (q ^ (d * d))⁻¹ * (q ^ pairExp g)⁻¹ ≤ vertexWeight q g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hhigh : autOrder q g ≤ q ^ (pairExp g + d * d) := by
    unfold autOrder
    calc q ^ endDim g * ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i)
        ≤ q ^ endDim g * 1 := by
          exact mul_le_mul_of_nonneg_left (prod_blockFactor_le_one g hq)
            (le_of_lt (pow_pos hq0 _))
      _ = q ^ endDim g := by ring
      _ ≤ q ^ (pairExp g + d * d) := pow_le_pow_right₀ hq.le (endDim_le_pairExp g)
  unfold vertexWeight
  rw [show (q ^ (d * d))⁻¹ * (q ^ pairExp g)⁻¹ = (q ^ (pairExp g + d * d))⁻¹ by
    rw [pow_add, mul_inv]; ring]
  exact inv_anti₀ (autOrder_pos g hq) hhigh

end Bounds

end PGLQuotient
-- ==== upstream: Packages/Catalog/Algebra/PGLQuotient/HeightThreshold.lean ====
/-!
# Integrability threshold for the lattice-minima height

Let `α` be the homothety-invariant normalised lattice-minima height on the standard
arithmetic quotient of the Bruhat–Tits building of `PGL_d(F_q((t^{-1})))`, modelled as in
`Algebra.PGLQuotient.VertexModel`.

The main theorem of this file is the *exact integrability threshold*

`Summable (fun g => vertexWeight q g * α g ^ s) ↔ s < d`,

i.e. `α ∈ L^r` precisely for `r < d` (in particular for `0 < r < d`).  The positive direction
is proved by factoring the majorant into a product of `d-1` independent geometric series over
the gap coordinates; the negative direction uses the cusp ray `λ = (n,0,…,0)`, along which the
mass decays exactly like `α^{-d}`.
-/

namespace PGLQuotient

open Finset

section PiGeom

/-- A product of independent geometric series over the lattice `Fin m → ℕ`. -/
lemma summable_pi_geom : ∀ {m : ℕ} (x : Fin m → ℝ), (∀ k, 0 ≤ x k) → (∀ k, x k < 1) →
    Summable (fun h : Fin m → ℕ => ∏ k, x k ^ h k) ∧
      ∑' h : Fin m → ℕ, ∏ k, x k ^ h k = ∏ k, (1 - x k)⁻¹ := by
  intro m
  induction m with
  | zero =>
      intro x _ _
      refine ⟨Summable.of_finite, ?_⟩
      simp
  | succ m ih =>
      intro x h0 h1
      obtain ⟨hs2, hv2⟩ := ih (fun k => x k.succ) (fun k => h0 _) (fun k => h1 _)
      have hsum1 : Summable (fun n : ℕ => x 0 ^ n) :=
        summable_geometric_of_lt_one (h0 0) (h1 0)
      have hnn1 : (0 : ℕ → ℝ) ≤ fun n : ℕ => x 0 ^ n := fun n => pow_nonneg (h0 0) n
      have hnn2 : (0 : (Fin m → ℕ) → ℝ) ≤ fun h : Fin m → ℕ => ∏ k : Fin m, x k.succ ^ h k :=
        fun h => Finset.prod_nonneg (fun k _ => pow_nonneg (h0 _) _)
      have hprod := hsum1.mul_of_nonneg hs2 hnn1 hnn2
      have key : ∀ p : ℕ × (Fin m → ℕ),
          (∏ k : Fin (m+1), x k ^ ((Fin.consEquiv (fun _ => ℕ)) p) k)
            = x 0 ^ p.1 * ∏ k : Fin m, x k.succ ^ p.2 k := by
        intro p
        rw [Fin.prod_univ_succ]
        simp [Fin.consEquiv_apply]
      have hcomp : Summable (fun p : ℕ × (Fin m → ℕ) =>
          ∏ k : Fin (m+1), x k ^ ((Fin.consEquiv (fun _ => ℕ)) p) k) := by
        simpa only [key] using hprod
      have hsummable : Summable (fun h : Fin (m+1) → ℕ => ∏ k, x k ^ h k) :=
        (Equiv.summable_iff (Fin.consEquiv (fun _ => ℕ))).mp hcomp
      refine ⟨hsummable, ?_⟩
      have hval : ∑' h : Fin (m+1) → ℕ, ∏ k, x k ^ h k
          = ∑' p : ℕ × (Fin m → ℕ), x 0 ^ p.1 * ∏ k : Fin m, x k.succ ^ p.2 k := by
        rw [← (Fin.consEquiv (fun _ => ℕ)).tsum_eq (fun h : Fin (m+1) → ℕ => ∏ k, x k ^ h k)]
        exact tsum_congr key
      have hslice : ∀ b : ℕ, Summable
          (fun c : Fin m → ℕ => x 0 ^ b * ∏ k : Fin m, x k.succ ^ c k) := fun b => hs2.mul_left _
      rw [hval, hprod.tsum_prod' hslice]
      rw [tsum_congr (fun n : ℕ => hs2.tsum_mul_left (x 0 ^ n)), tsum_mul_right, hv2,
        tsum_geometric_of_lt_one (h0 0) (h1 0), Fin.prod_univ_succ]

end PiGeom

section Threshold

variable {d : ℕ} {q : ℝ}

lemma gapAt_coe (g : Vertex d) (k : Fin (d - 1)) : gapAt g (k : ℕ) = g k := by
  simp [gapAt, k.isLt]

-- [dropped: platform already declares gapRatio]
lemma height_pow (hq : 1 < q) (g : Vertex d) (s : ℝ) :
    height q g ^ s = (q ^ (s / d)) ^ heightExp g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  unfold height
  rw [← Real.rpow_natCast (q ^ (s / d)) (heightExp g), ← Real.rpow_mul hq0.le,
    ← Real.rpow_mul hq0.le]
  congr 1
  ring

lemma prod_gapRatio (s : ℝ) (g : Vertex d) :
    ∏ k, gapRatio q d s k ^ g k = (q ^ pairExp g)⁻¹ * (q ^ (s / d)) ^ heightExp g := by
  have hterm : ∀ k : Fin (d - 1), gapRatio q d s k ^ g k
      = (q⁻¹) ^ ((((k : ℕ) + 1) * (d - 1 - (k : ℕ))) * g k)
        * (q ^ (s / d)) ^ ((d - 1 - (k : ℕ)) * g k) := by
    intro k
    unfold gapRatio
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul]
  rw [Finset.prod_congr rfl (fun k _ => hterm k), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← inv_pow]
  congr 2
  · rw [pairExp, ← Fin.sum_univ_eq_sum_range (fun k => (k + 1) * (d - 1 - k) * gapAt g k)]
    exact Finset.sum_congr rfl (fun k _ => by rw [gapAt_coe, mul_assoc])
  · rw [heightExp, ← Fin.sum_univ_eq_sum_range (fun k => (d - 1 - k) * gapAt g k)]
    exact Finset.sum_congr rfl (fun k _ => by rw [gapAt_coe])

lemma gapRatio_nonneg (hq : 1 < q) (s : ℝ) (k : Fin (d - 1)) : 0 ≤ gapRatio q d s k := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  unfold gapRatio
  positivity

lemma gapRatio_lt_one (hq : 1 < q) (hd : 2 ≤ d) {s : ℝ} (hs : s < d) (k : Fin (d - 1)) :
    gapRatio q d s k < 1 := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hd0 : (0:ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hcq : q ^ (s / d) < q := by
    have h1 : s / d < 1 := by rw [div_lt_one hd0]; exact hs
    calc q ^ (s / d) < q ^ (1:ℝ) := by
          exact (Real.rpow_lt_rpow_left_iff hq).mpr h1
      _ = q := Real.rpow_one q
  have hcpos : (0:ℝ) < q ^ (s / d) := Real.rpow_pos_of_pos hq0 _
  set m : ℕ := d - 1 - (k : ℕ) with hm
  have hm1 : 1 ≤ m := by have := k.isLt; omega
  have h1 : (q ^ (s / d)) ^ m < q ^ m :=
    pow_lt_pow_left₀ hcq (le_of_lt hcpos) (by omega)
  have h2 : q ^ m ≤ q ^ (((k : ℕ) + 1) * m) :=
    pow_le_pow_right₀ hq.le (by nlinarith [Nat.le_mul_of_pos_left m (Nat.succ_pos (k : ℕ))])
  unfold gapRatio
  rw [← hm, inv_mul_lt_one₀ (pow_pos hq0 _)]
  calc (q ^ (s / d)) ^ m < q ^ m := h1
    _ ≤ q ^ (((k : ℕ) + 1) * m) := h2

/-- Positive direction of the integrability threshold. -/
theorem summable_weight_height_of_lt (hq : 1 < q) (hd : 2 ≤ d) {s : ℝ} (hs : s < d) :
    Summable (fun g : Vertex d => vertexWeight q g * height q g ^ s) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  obtain ⟨hsum, -⟩ := summable_pi_geom (gapRatio q d s)
    (gapRatio_nonneg hq s) (gapRatio_lt_one hq hd hs)
  refine Summable.of_nonneg_of_le (fun g => ?_) (fun g => ?_)
    (hsum.mul_left (((1 - q⁻¹) ^ d)⁻¹))
  · exact mul_nonneg (le_of_lt (vertexWeight_pos g hq))
      (le_of_lt (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hq0 _) s))
  · rw [height_pow hq g s, prod_gapRatio s g, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (vertexWeight_le g hq)
      (pow_nonneg (le_of_lt (Real.rpow_pos_of_pos hq0 _)) _)

-- [dropped: platform already declares rayVertex]
lemma gapAt_ray (hd : 2 ≤ d) (n k : ℕ) :
    gapAt (rayVertex d n) k = if k = 0 then n else 0 := by
  unfold gapAt rayVertex
  by_cases hk : k < d - 1
  · rw [dif_pos hk]
  · rw [dif_neg hk]
    have hk0 : k ≠ 0 := by omega
    simp [hk0]

lemma heightExp_ray (hd : 2 ≤ d) (n : ℕ) : heightExp (rayVertex d n) = (d - 1) * n := by
  unfold heightExp
  rw [Finset.sum_eq_single 0]
  · rw [gapAt_ray hd]
    simp
  · intro k _ hk
    rw [gapAt_ray hd]
    simp [hk]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

lemma pairExp_ray (hd : 2 ≤ d) (n : ℕ) : pairExp (rayVertex d n) = (d - 1) * n := by
  unfold pairExp
  rw [Finset.sum_eq_single 0]
  · rw [gapAt_ray hd]
    simp
  · intro k _ hk
    rw [gapAt_ray hd]
    simp [hk]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

lemma rayVertex_injective (hd : 2 ≤ d) : Function.Injective (rayVertex d) := by
  intro m n hmn
  have h0 : (0 : ℕ) < d - 1 := by omega
  have := congrFun hmn ⟨0, h0⟩
  simpa [rayVertex] using this

/-- Negative direction of the integrability threshold. -/
theorem not_summable_weight_height_of_ge (hq : 1 < q) (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) ≤ s) :
    ¬ Summable (fun g : Vertex d => vertexWeight q g * height q g ^ s) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hd0 : (0:ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  intro hsum
  have hcomp : Summable (fun n : ℕ => vertexWeight q (rayVertex d n)
      * height q (rayVertex d n) ^ s) := hsum.comp_injective (rayVertex_injective hd)
  -- every term along the ray is at least `q^{-d^2}`
  have hcq : q ≤ q ^ (s / d) := by
    have h1 : (1:ℝ) ≤ s / d := by rw [le_div_iff₀ hd0]; linarith
    calc q = q ^ (1:ℝ) := (Real.rpow_one q).symm
      _ ≤ q ^ (s / d) := by
          exact Real.rpow_le_rpow_left_iff hq |>.mpr h1
  have hlow : ∀ n : ℕ, (q ^ (d * d))⁻¹
      ≤ vertexWeight q (rayVertex d n) * height q (rayVertex d n) ^ s := by
    intro n
    have hw := vertexWeight_ge (rayVertex d n) hq
    rw [height_pow hq _ s, heightExp_ray hd, pairExp_ray hd] at *
    have hpow : q ^ ((d - 1) * n) ≤ (q ^ (s / d)) ^ ((d - 1) * n) :=
      pow_le_pow_left₀ (le_of_lt hq0) hcq _
    calc (q ^ (d * d))⁻¹
        = (q ^ (d * d))⁻¹ * ((q ^ ((d - 1) * n))⁻¹ * q ^ ((d - 1) * n)) := by
          rw [inv_mul_cancel₀ (ne_of_gt (pow_pos hq0 _)), mul_one]
      _ ≤ (q ^ (d * d))⁻¹ * ((q ^ ((d - 1) * n))⁻¹ * (q ^ (s / d)) ^ ((d - 1) * n)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((q ^ (d * d))⁻¹ * (q ^ ((d - 1) * n))⁻¹) * (q ^ (s / d)) ^ ((d - 1) * n) := by ring
      _ ≤ vertexWeight q (rayVertex d n) * (q ^ (s / d)) ^ ((d - 1) * n) := by
          refine mul_le_mul_of_nonneg_right hw ?_
          positivity
  have htend := hcomp.tendsto_atTop_zero
  have hpos : (0:ℝ) < (q ^ (d * d))⁻¹ := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend ((q ^ (d * d))⁻¹) hpos
  have h1 := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h1
  have h2 := hlow N
  have h3 : |vertexWeight q (rayVertex d N) * height q (rayVertex d N) ^ s|
      = vertexWeight q (rayVertex d N) * height q (rayVertex d N) ^ s := by
    refine abs_of_nonneg (mul_nonneg (le_of_lt (vertexWeight_pos _ hq)) ?_)
    exact le_of_lt (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hq0 _) s)
  rw [h3] at h1
  linarith

/-- **Exact integrability threshold.**  The normalised lattice-minima height `α` has a finite
`s`-th moment on the standard arithmetic quotient of `PGL_d` precisely when `s < d`. -/
theorem summable_weight_height_iff (hq : 1 < q) (hd : 2 ≤ d) (s : ℝ) :
    Summable (fun g : Vertex d => vertexWeight q g * height q g ^ s) ↔ s < d := by
  constructor
  · intro hsum
    by_contra hcon
    exact not_summable_weight_height_of_ge hq hd (not_lt.mp hcon) hsum
  · exact summable_weight_height_of_lt hq hd

end Threshold

end PGLQuotient
-- ==== upstream: Packages/Catalog/Algebra/PGLQuotient/TwistedWeight.lean ====
/-!
# The twisted vertex mass and its row-peeling recursion

To compute the vertex volume of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))`
in arbitrary rank we enlarge the vertex mass `1/|Aut λ|` to a two-parameter family.

For a vertex `λ` of rank `d` (in the gap model of `Algebra.PGLQuotient.VertexModel`) put

* `sigmaExp λ = ∑_i (λ_0 - λ_i)` — the "top-row defect";
* `firstBlockSize λ = #{ i : λ_i = λ_0 }` — the size of the block of maximal entries;
* `blockProdShift q j λ = ∏_i (1 - q^{-(r_i + j·[λ_i = λ_0])})` — the Levi factor with the
  ranks in the top block shifted by `j`;
* `twWeight q c j λ = (q^{dim End + c·σ + j·m} · blockProdShift q j λ)⁻¹`.

For `c = j = 0` this is exactly the vertex mass: `twWeight q 0 0 = vertexWeight q`
(`twWeight_zero_zero`).

The point of the two extra parameters is that the family is *stable under peeling off the top
row of `λ`*: writing a rank-`(n+2)` vertex as `Fin.cons a λ'` with `a = λ_0 - λ_1 ≥ 0` the gap
between the first row and the rest, one gets (`twWeight_cons_zero`, `twWeight_cons_succ`)

`twWeight q c j (cons 0 λ') = K · twWeight q (c+1) (j+1) λ'`,
`twWeight q c j (cons (a+1) λ') = K · q^{-(n+1)(c+1)(a+1)} · twWeight q (c+1) 0 λ'`,

with `K = (q^{n+2+j}(1 - q^{-(1+j)}))⁻¹`.  This is the recursion which, summed over all
vertices, produces the closed product form of the vertex volume.
-/

namespace PGLQuotient

open Finset

variable {d : ℕ}

-- [dropped: platform already declares sigmaExp]
-- [dropped: platform already declares firstBlockSize]
-- [dropped: platform already declares blockProdShift]
-- [dropped: platform already declares twWeight]
section Basic

variable {q : ℝ}

lemma blockProdShift_zero (g : Vertex d) :
    blockProdShift q 0 g = ∏ i ∈ range d, (1 - q⁻¹ ^ blockRank g i) := by
  unfold blockProdShift
  exact Finset.prod_congr rfl (fun i _ => by simp)

/-- For the untwisted parameters the twisted mass is the vertex mass. -/
lemma twWeight_zero_zero (g : Vertex d) : twWeight q 0 0 g = vertexWeight q g := by
  unfold twWeight vertexWeight autOrder
  rw [blockProdShift_zero]
  simp

/-- Every Levi factor `1 - q^{-r}` with `r ≥ 1` is positive. -/
lemma one_sub_inv_pow_pos (hq : 1 < q) {r : ℕ} (hr : 1 ≤ r) : 0 < 1 - q⁻¹ ^ r := by
  have h1 : q⁻¹ ^ r ≤ q⁻¹ ^ 1 :=
    pow_le_pow_of_le_one (le_of_lt (inv_pos.mpr (lt_trans zero_lt_one hq)))
      (le_of_lt (inv_lt_one_of_one_lt hq)) hr
  have h2 : q⁻¹ < 1 := inv_lt_one_of_one_lt hq
  simp only [pow_one] at h1
  linarith

/-- The Levi factors increase with the shift. -/
lemma one_sub_inv_pow_mono (hq : 1 < q) {r s : ℕ} (hrs : r ≤ s) :
    1 - q⁻¹ ^ r ≤ 1 - q⁻¹ ^ s := by
  have h1 : q⁻¹ ^ s ≤ q⁻¹ ^ r :=
    pow_le_pow_of_le_one (le_of_lt (inv_pos.mpr (lt_trans zero_lt_one hq)))
      (le_of_lt (inv_lt_one_of_one_lt hq)) hrs
  linarith

lemma blockProdShift_pos (hq : 1 < q) (j : ℕ) (g : Vertex d) : 0 < blockProdShift q j g :=
  Finset.prod_pos (fun i _ => one_sub_inv_pow_pos hq (by have := one_le_blockRank g i; omega))

lemma twWeight_pos (hq : 1 < q) (c j : ℕ) (g : Vertex d) : 0 < twWeight q c j g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  exact inv_pos.mpr (mul_pos (pow_pos hq0 _) (blockProdShift_pos hq j g))

/-- Twisting only decreases the mass. -/
lemma twWeight_le_vertexWeight (hq : 1 < q) (c j : ℕ) (g : Vertex d) :
    twWeight q c j g ≤ vertexWeight q g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hvw : vertexWeight q g = (q ^ endDim g * blockProdShift q 0 g)⁻¹ := by
    rw [blockProdShift_zero]
    rfl
  have h0 : 0 < q ^ endDim g * blockProdShift q 0 g :=
    mul_pos (pow_pos hq0 _) (blockProdShift_pos hq 0 g)
  have hBP : blockProdShift q 0 g ≤ blockProdShift q j g := by
    unfold blockProdShift
    refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
    · exact le_of_lt (one_sub_inv_pow_pos hq
        (by have := one_le_blockRank g i; split_ifs <;> omega))
    · exact one_sub_inv_pow_mono hq (by split_ifs <;> omega)
  have hle : q ^ endDim g * blockProdShift q 0 g
      ≤ q ^ (endDim g + c * sigmaExp g + j * firstBlockSize g) * blockProdShift q j g :=
    mul_le_mul (pow_le_pow_right₀ hq.le (by omega)) hBP
      (le_of_lt (blockProdShift_pos hq 0 g)) (le_of_lt (pow_pos hq0 _))
  rw [hvw]
  exact inv_anti₀ h0 hle

end Basic

section Peeling

variable {n : ℕ}

-- [dropped: platform already declares consV]
/-- Peeling the first index off a filtered cardinality over a range. -/
lemma card_filter_range_succ (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    ((range (N + 1)).filter p).card
      = ((range N).filter (fun i => p (i + 1))).card + (if p 0 then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']

lemma gapAt_consV_zero (a : ℕ) (g : Vertex (n + 1)) : gapAt (consV a g) 0 = a := by
  simp [gapAt, consV]

lemma gapAt_consV_succ (a : ℕ) (g : Vertex (n + 1)) (k : ℕ) :
    gapAt (consV a g) (k + 1) = gapAt g k := by
  unfold gapAt consV
  by_cases hk : k < n
  · rw [dif_pos (show k + 1 < n + 2 - 1 by omega), dif_pos (show k < n + 1 - 1 by omega)]
    rfl
  · rw [dif_neg (show ¬ k + 1 < n + 2 - 1 by omega), dif_neg (show ¬ k < n + 1 - 1 by omega)]

lemma lam_cons_succ (a : ℕ) (g : Vertex (n + 1)) (i : ℕ) :
    lam (consV a g) (i + 1) = lam g i := by
  unfold lam
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range,
    show n + 2 - 1 - (i + 1) = n + 1 - 1 - i by omega]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [show i + 1 + t = (i + t) + 1 by omega, gapAt_consV_succ]

lemma lam_cons_zero (a : ℕ) (g : Vertex (n + 1)) :
    lam (consV a g) 0 = a + lam g 0 := by
  unfold lam
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.sub_zero, Nat.zero_add, Nat.add_sub_cancel]
  rw [show n + 2 - 1 = n + 1 from rfl,
    Finset.sum_range_succ' (fun t => gapAt (consV a g) t) n, gapAt_consV_zero,
    Finset.sum_congr rfl (fun t _ => gapAt_consV_succ a g t), Nat.add_comm]

lemma sigmaExp_cons (a : ℕ) (g : Vertex (n + 1)) :
    sigmaExp (consV a g) = (n + 1) * a + sigmaExp g := by
  unfold sigmaExp
  rw [Finset.sum_range_succ' (fun i => lam (consV a g) 0 - lam (consV a g) i) (n + 1)]
  simp only [Nat.sub_self, Nat.add_zero]
  have hterm : ∀ i ∈ range (n + 1),
      lam (consV a g) 0 - lam (consV a g) (i + 1) = a + (lam g 0 - lam g i) := by
    intro i _
    rw [lam_cons_succ, lam_cons_zero]
    have := lam_antitone g (Nat.zero_le i)
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul]

lemma firstBlockSize_cons (a : ℕ) (g : Vertex (n + 1)) :
    firstBlockSize (consV a g)
      = (if a = 0 then firstBlockSize g else 0) + 1 := by
  unfold firstBlockSize
  rw [card_filter_range_succ (fun i => lam (consV a g) i = lam (consV a g) 0) (n + 1), if_pos rfl]
  congr 1
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    congr 1
    refine Finset.filter_congr (fun i _ => ?_)
    rw [lam_cons_succ, lam_cons_zero, Nat.zero_add]
  · rw [if_neg ha]
    have : (range (n + 1)).filter (fun i => lam (consV a g) (i + 1) = lam (consV a g) 0) = ∅ := by
      refine Finset.filter_false_of_mem (fun i _ => ?_)
      rw [lam_cons_succ, lam_cons_zero]
      have := lam_antitone g (Nat.zero_le i)
      omega
    rw [this, Finset.card_empty]

/-- The number of rows of `λ'` tied with the top row, seen from the prepended row. -/
lemma sum_tie_cons (a : ℕ) (g : Vertex (n + 1)) :
    ∑ i ∈ range (n + 1), (lam g i + 1 - (a + lam g 0))
      = (if a = 0 then firstBlockSize g else 0) := by
  have hterm : ∀ i ∈ range (n + 1),
      lam g i + 1 - (a + lam g 0) = (if lam g i = a + lam g 0 then 1 else 0) := by
    intro i _
    have := lam_antitone g (Nat.zero_le i)
    by_cases h : lam g i = a + lam g 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  rw [Finset.sum_congr rfl hterm]
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    unfold firstBlockSize
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun i _ => by rw [Nat.zero_add])
  · rw [if_neg ha]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have := lam_antitone g (Nat.zero_le i)
    rw [if_neg (by omega)]

lemma endDim_cons (a : ℕ) (g : Vertex (n + 1)) :
    endDim (consV a g)
      = endDim g + (n + 2) + (n + 1) * a + sigmaExp g
        + (if a = 0 then firstBlockSize g else 0) := by
  unfold endDim
  have hinner : ∀ i : ℕ, ∑ j ∈ range (n + 2), (lam (consV a g) i + 1 - lam (consV a g) j)
      = (∑ j ∈ range (n + 1), (lam (consV a g) i + 1 - lam g j))
        + (lam (consV a g) i + 1 - (a + lam g 0)) := by
    intro i
    rw [Finset.sum_range_succ' (fun j => lam (consV a g) i + 1 - lam (consV a g) j) (n + 1),
      lam_cons_zero]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [lam_cons_succ])
  rw [Finset.sum_range_succ'
    (fun i => ∑ j ∈ range (n + 2), (lam (consV a g) i + 1 - lam (consV a g) j)) (n + 1),
    hinner 0, lam_cons_zero]
  have hrest : ∀ i ∈ range (n + 1),
      (∑ j ∈ range (n + 2), (lam (consV a g) (i + 1) + 1 - lam (consV a g) j))
        = (∑ j ∈ range (n + 1), (lam g i + 1 - lam g j))
          + (lam g i + 1 - (a + lam g 0)) := by
    intro i _
    rw [hinner (i + 1), lam_cons_succ]
  rw [Finset.sum_congr rfl hrest, Finset.sum_add_distrib, sum_tie_cons]
  have htop : ∑ j ∈ range (n + 1), (a + lam g 0 + 1 - lam g j)
      = (n + 1) * (a + 1) + sigmaExp g := by
    have hterm : ∀ j ∈ range (n + 1),
        a + lam g 0 + 1 - lam g j = (a + 1) + (lam g 0 - lam g j) := by
      intro j _
      have := lam_antitone g (Nat.zero_le j)
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul]
    rfl
  rw [htop, show a + lam g 0 + 1 - (a + lam g 0) = 1 from by omega]
  ring

lemma blockRank_consV_zero (a : ℕ) (g : Vertex (n + 1)) : blockRank (consV a g) 0 = 1 := by
  unfold blockRank
  simp [Finset.filter_singleton]

lemma blockRank_consV_succ (a : ℕ) (g : Vertex (n + 1)) (i : ℕ) :
    blockRank (consV a g) (i + 1)
      = blockRank g i + (if a = 0 ∧ lam g i = lam g 0 then 1 else 0) := by
  unfold blockRank
  rw [card_filter_range_succ (fun k => lam (consV a g) k = lam (consV a g) (i + 1)) (i + 1)]
  congr 1
  · congr 1
    refine Finset.filter_congr (fun k _ => ?_)
    rw [lam_cons_succ, lam_cons_succ]
  · rw [lam_cons_zero, lam_cons_succ]
    have := lam_antitone g (Nat.zero_le i)
    by_cases ha : a = 0
    · subst ha
      by_cases h : lam g i = lam g 0
      · rw [if_pos (by omega), if_pos ⟨rfl, h⟩]
      · rw [if_neg (by omega), if_neg (by simp [h])]
    · rw [if_neg (by omega), if_neg (by simp [ha])]

lemma blockProdShift_cons (q : ℝ) (j a : ℕ) (g : Vertex (n + 1)) :
    blockProdShift q j (consV a g)
      = (1 - q⁻¹ ^ (1 + j)) *
        (if a = 0 then blockProdShift q (j + 1) g else blockProdShift q 0 g) := by
  unfold blockProdShift
  rw [Finset.prod_range_succ'
    (fun i => 1 - q⁻¹ ^ (blockRank (consV a g) i
      + (if lam (consV a g) i = lam (consV a g) 0 then j else 0))) (n + 1),
    blockRank_consV_zero, if_pos rfl, mul_comm]
  congr 1
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [blockRank_consV_succ, lam_cons_succ, lam_cons_zero, Nat.zero_add]
    by_cases h : lam g i = lam g 0
    · rw [if_pos ⟨rfl, h⟩, if_pos h, if_pos h]
      congr 2
      omega
    · rw [if_neg (by simp [h]), if_neg h, if_neg h]
  · rw [if_neg ha]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [blockRank_consV_succ, lam_cons_succ, lam_cons_zero]
    have := lam_antitone g (Nat.zero_le i)
    rw [if_neg (by simp [ha]), if_neg (show ¬ lam g i = a + lam g 0 by omega)]
    simp

variable {q : ℝ}

/-- Peeling a top row with zero gap. -/
lemma twWeight_cons_zero (hq : 1 < q) (c j : ℕ) (g : Vertex (n + 1)) :
    twWeight q c j (consV 0 g)
      = (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹ * twWeight q (c + 1) (j + 1) g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  unfold twWeight
  rw [endDim_cons, sigmaExp_cons, firstBlockSize_cons, blockProdShift_cons]
  simp only [reduceIte]
  rw [show endDim g + (n + 2) + (n + 1) * 0 + sigmaExp g + firstBlockSize g
      + c * ((n + 1) * 0 + sigmaExp g) + j * (firstBlockSize g + 1)
      = (endDim g + (c + 1) * sigmaExp g + (j + 1) * firstBlockSize g) + (n + 2 + j) by ring]
  rw [← mul_inv]
  congr 1
  rw [pow_add]
  ring

/-- Peeling a top row with positive gap. -/
lemma twWeight_cons_succ (hq : 1 < q) (c j a : ℕ) (g : Vertex (n + 1)) :
    twWeight q c j (consV (a + 1) g)
      = (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹
        * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * twWeight q (c + 1) 0 g := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hane : ¬ (a + 1 = 0) := by omega
  unfold twWeight
  rw [endDim_cons, sigmaExp_cons, firstBlockSize_cons, blockProdShift_cons]
  simp only [if_neg hane]
  rw [show endDim g + (n + 2) + (n + 1) * (a + 1) + sigmaExp g + 0
      + c * ((n + 1) * (a + 1) + sigmaExp g) + j * (0 + 1)
      = (endDim g + (c + 1) * sigmaExp g + 0 * firstBlockSize g)
        + (n + 2 + j) + (n + 1) * (c + 1) * (a + 1) by ring]
  rw [← mul_inv, ← mul_inv]
  congr 1
  rw [pow_add, pow_add, ← pow_mul]
  ring

end Peeling

end PGLQuotient
-- ==== upstream: Packages/Catalog/Algebra/PGLQuotient/VolumeAlgebra.lean ====
/-!
# The algebraic core of the general-rank vertex volume

This file contains the purely algebraic input for the closed product form of the vertex volume
of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))` in **arbitrary rank**.

The building-theoretic side (see `Algebra.PGLQuotient.TwistedWeight` and
`Algebra.PGLQuotient.VertexVolumeGeneral`) produces a two-parameter family of *twisted masses*
`M(n,c,j)` (rank `n+1`, twist parameters `c` and `j`) satisfying a row-peeling recursion.  The
solution of that recursion is

`M(n,c,j) = NumV q n c j / DenV q n c j`,

where

* `NumV q n c j = ∑_{i=0}^{n} q^{ci} (∏_{k<i} (q^{n-k}-1)) (∏_{s<n-i}(q^{s+1+j}-1))`,
* `DenV q n c j = (∏_{s<n+1}(q^{s+1+j}-1)) (∏_{k<n}(q^{k+1}-1)) (∏_{k<n}(q^{c+k+1}-1))`.

The main result here is the **cut-set recursion** `NumV_rec`:

`q^{m+1} · NumV q (m+1) c j = (q^{m+1}-1)(q^{c+1}-1) · NumV q m (c+1) (j+1) + Jfac q (m+1) (j+1)`,

proved by an Abel summation whose term-by-term input is a pair of product identities.
Specialising `c = j = 0` collapses `NumV` to `(n+1)·Pfac q n`, which is what produces the
closed product form `d/(P(d)P(d-1))` of the vertex volume.
-/

namespace PGLQuotient

open Finset

section VolumeAlgebra

variable (q : ℝ)

-- [dropped: platform already declares Gpoly]
-- [dropped: platform already declares Jfac]
-- [dropped: platform already declares Pfac]
-- [dropped: platform already declares Cfac]
-- [dropped: platform already declares NumV]
-- [dropped: platform already declares DenV]
variable {q}

lemma Jfac_zero_right (r : ℕ) : Jfac q r 0 = Pfac q r := by
  unfold Jfac Pfac
  exact Finset.prod_congr rfl (fun s _ => by rw [Nat.add_zero])

lemma Jfac_succ (r j : ℕ) : Jfac q (r + 1) j = (q ^ (1 + j) - 1) * Jfac q r (j + 1) := by
  unfold Jfac
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  exact Finset.prod_congr rfl
    (fun s _ => by rw [show s + 1 + 1 + j = s + 1 + (j + 1) from by omega])

lemma Pfac_succ (n : ℕ) : Pfac q (n + 1) = Pfac q n * (q ^ (n + 1) - 1) := by
  unfold Pfac; rw [Finset.prod_range_succ]

lemma Cfac_succ (n c : ℕ) : Cfac q (n + 1) c = (q ^ (c + 1) - 1) * Cfac q n (c + 1) := by
  unfold Cfac
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  exact Finset.prod_congr rfl
    (fun k _ => by rw [show c + (k + 1) + 1 = c + 1 + k + 1 from by omega])

lemma Gpoly_succ_left (n i : ℕ) : Gpoly q (n + 1) (i + 1) = (q ^ (n + 1) - 1) * Gpoly q n i := by
  unfold Gpoly
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  exact Finset.prod_congr rfl (fun k _ => by rw [Nat.succ_sub_succ])

lemma Jfac_succ_right (r j : ℕ) : Jfac q (r + 1) j = Jfac q r j * (q ^ (r + 1 + j) - 1) := by
  unfold Jfac; rw [Finset.prod_range_succ]

lemma Gpoly_succ_right (n i : ℕ) : Gpoly q n (i + 1) = Gpoly q n i * (q ^ (n - i) - 1) := by
  unfold Gpoly; rw [Finset.prod_range_succ]

lemma Gpoly_zero (n : ℕ) : Gpoly q n 0 = 1 := by simp [Gpoly]

lemma Jfac_zero (j : ℕ) : Jfac q 0 j = 1 := by simp [Jfac]

/-- Beyond the diagonal the descending product vanishes. -/
lemma Gpoly_self_succ (m : ℕ) : Gpoly q m (m + 1) = 0 := by
  unfold Gpoly
  refine Finset.prod_eq_zero (Finset.self_mem_range_succ m) ?_
  simp

lemma Gpoly_mul_Jfac_zero {n i : ℕ} (hi : i ≤ n) :
    Gpoly q n i * Jfac q (n - i) 0 = Pfac q n := by
  induction i with
  | zero => rw [Gpoly_zero, one_mul, Nat.sub_zero, Jfac_zero_right]
  | succ i ih =>
      have hi' : i ≤ n := by omega
      have hstep : Jfac q (n - i) 0 = Jfac q (n - (i + 1)) 0 * (q ^ (n - i) - 1) := by
        rw [show n - i = (n - (i + 1)) + 1 from by omega, Jfac_succ_right, Nat.add_zero]
      have := ih hi'
      rw [hstep] at this
      rw [Gpoly_succ_right]
      calc Gpoly q n i * (q ^ (n - i) - 1) * Jfac q (n - (i + 1)) 0
          = Gpoly q n i * (Jfac q (n - (i + 1)) 0 * (q ^ (n - i) - 1)) := by ring
        _ = Pfac q n := this

lemma NumV_zero_right (n c : ℕ) : NumV q n c 0 = Pfac q n * ∑ i ∈ range (n + 1), q ^ (c * i) := by
  unfold NumV
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Gpoly_mul_Jfac_zero (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  ring

/-- The one-step difference identity behind the Abel summation. -/
lemma jfac_diff (t j : ℕ) :
    Jfac q t (j + 1) - (q ^ t - 1) * Jfac q (t - 1) (j + 1) = q ^ t * Jfac q t j := by
  cases t with
  | zero => simp [Jfac_zero]
  | succ t =>
      rw [Nat.add_sub_cancel, Jfac_succ_right t (j + 1), Jfac_succ t j]
      have hpow : q ^ (t + 1 + (j + 1)) = q ^ (t + 1) * q ^ (1 + j) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      ring

/-- The `i = 0` term of the Abel summation. -/
lemma abel_zero (m j : ℕ) :
    q ^ (m + 1) * (Gpoly q (m + 1) 0 * Jfac q (m + 1 - 0) j)
      = Jfac q (m + 1) (j + 1) - (q ^ (m + 1) - 1) * (Gpoly q m 0 * Jfac q (m - 0) (j + 1)) := by
  rw [Gpoly_zero, Gpoly_zero, one_mul, one_mul, Nat.sub_zero, Nat.sub_zero]
  have h := jfac_diff (q := q) (m + 1) j
  rw [Nat.add_sub_cancel] at h
  linarith

/-- The generic term of the Abel summation. -/
lemma abel_succ {m i : ℕ} (hi : i ≤ m) (j : ℕ) :
    q ^ (m + 1) * (Gpoly q (m + 1) (i + 1) * Jfac q (m + 1 - (i + 1)) j)
      = q ^ (i + 1) * (q ^ (m + 1) - 1) *
        (Gpoly q m i * Jfac q (m - i) (j + 1)
          - Gpoly q m (i + 1) * Jfac q (m - (i + 1)) (j + 1)) := by
  have hsub : m + 1 - (i + 1) = m - i := by omega
  have hsub2 : m - (i + 1) = (m - i) - 1 := by omega
  have hpow : q ^ (i + 1) * q ^ (m - i) = q ^ (m + 1) := by
    rw [← pow_add]; congr 1; omega
  have hcore := jfac_diff (q := q) (m - i) j
  have key : q ^ (m + 1) * Jfac q (m - i) j
      = q ^ (i + 1) * (Jfac q (m - i) (j + 1)
        - (q ^ (m - i) - 1) * Jfac q ((m - i) - 1) (j + 1)) := by
    rw [hcore, ← hpow]; ring
  rw [Gpoly_succ_left, Gpoly_succ_right, hsub, hsub2]
  linear_combination ((q ^ (m + 1) - 1) * Gpoly q m i) * key

/-- **The cut-set recursion.** -/
theorem NumV_rec (m c j : ℕ) :
    q ^ (m + 1) * NumV q (m + 1) c j
      = (q ^ (m + 1) - 1) * (q ^ (c + 1) - 1) * NumV q m (c + 1) (j + 1)
        + Jfac q (m + 1) (j + 1) := by
  set u : ℕ → ℝ := fun i => Gpoly q m i * Jfac q (m - i) (j + 1) with hu
  have hutop : u (m + 1) = 0 := by simp [hu, Gpoly_self_succ]
  have hNum : NumV q m (c + 1) (j + 1) = ∑ i ∈ range (m + 1), q ^ ((c + 1) * i) * u i :=
    Finset.sum_congr rfl (fun i _ => by rw [hu])
  -- Abel summation: the shifted sum
  have hshift : (∑ i ∈ range (m + 1), q ^ (c * i) * q ^ i * u i) - u 0
      = ∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * u (i + 1) := by
    rw [Finset.sum_range_succ' (fun i => q ^ (c * i) * q ^ i * u i) m,
      Finset.sum_range_succ (fun i => q ^ (c * (i + 1)) * q ^ (i + 1) * u (i + 1)) m, hutop]
    simp
  have hAC : (∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * u i)
        - (∑ i ∈ range (m + 1), q ^ (c * i) * q ^ i * u i)
      = (q ^ (c + 1) - 1) * ∑ i ∈ range (m + 1), q ^ ((c + 1) * i) * u i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : q ^ (c * (i + 1)) * q ^ (i + 1) = q ^ ((c + 1) * i) * q ^ (c + 1) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    have h2 : q ^ (c * i) * q ^ i = q ^ ((c + 1) * i) := by
      rw [← pow_add]; congr 1; ring
    rw [h1, h2]; ring
  have hclaim : (∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * (u i - u (i + 1))) - u 0
      = (q ^ (c + 1) - 1) * ∑ i ∈ range (m + 1), q ^ ((c + 1) * i) * u i := by
    have hsplit : (∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * (u i - u (i + 1)))
        = (∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * u i)
          - ∑ i ∈ range (m + 1), q ^ (c * (i + 1)) * q ^ (i + 1) * u (i + 1) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit, ← hshift]
    linarith [hAC]
  -- the left-hand side, term by term
  have hL : q ^ (m + 1) * NumV q (m + 1) c j
      = ∑ i ∈ range (m + 1 + 1), q ^ (c * i) *
          (q ^ (m + 1) * (Gpoly q (m + 1) i * Jfac q (m + 1 - i) j)) := by
    unfold NumV
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hL, Finset.sum_range_succ' (fun i => q ^ (c * i) *
      (q ^ (m + 1) * (Gpoly q (m + 1) i * Jfac q (m + 1 - i) j))) (m + 1)]
  have hzero : q ^ (c * 0) * (q ^ (m + 1) * (Gpoly q (m + 1) 0 * Jfac q (m + 1 - 0) j))
      = Jfac q (m + 1) (j + 1) - (q ^ (m + 1) - 1) * u 0 := by
    rw [Nat.mul_zero, pow_zero, one_mul, abel_zero, hu]
  have hgen : ∀ i ∈ range (m + 1),
      q ^ (c * (i + 1)) * (q ^ (m + 1) * (Gpoly q (m + 1) (i + 1) * Jfac q (m + 1 - (i + 1)) j))
        = (q ^ (m + 1) - 1) * (q ^ (c * (i + 1)) * q ^ (i + 1) * (u i - u (i + 1))) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [abel_succ hi' j, hu]
    ring
  rw [Finset.sum_congr rfl hgen, hzero, ← Finset.mul_sum, hNum]
  linear_combination (q ^ (m + 1) - 1) * hclaim

section Positivity

variable (hq : 1 < q)
include hq

lemma Jfac_pos (r j : ℕ) : 0 < Jfac q r j := by
  refine Finset.prod_pos (fun s _ => ?_)
  have : (1 : ℝ) < q ^ (s + 1 + j) := one_lt_pow₀ hq (by omega)
  linarith

lemma Pfac_pos (n : ℕ) : 0 < Pfac q n := by
  refine Finset.prod_pos (fun k _ => ?_)
  have : (1 : ℝ) < q ^ (k + 1) := one_lt_pow₀ hq (by omega)
  linarith

lemma Cfac_pos (n c : ℕ) : 0 < Cfac q n c := by
  refine Finset.prod_pos (fun k _ => ?_)
  have : (1 : ℝ) < q ^ (c + k + 1) := one_lt_pow₀ hq (by omega)
  linarith

lemma DenV_pos (n c j : ℕ) : 0 < DenV q n c j :=
  mul_pos (mul_pos (Jfac_pos hq _ _) (Pfac_pos hq _)) (Cfac_pos hq _ _)

lemma one_lt_pow_succ (k : ℕ) : (1:ℝ) < q ^ (k + 1) := one_lt_pow₀ hq (by omega)

/-- The closed form `NumV/DenV` solves the row-peeling recursion: this is the algebraic
content of the induction step. -/
lemma NumDen_step (m c j : ℕ) :
    (q ^ (m + 1) * (q ^ (j + 1) - 1))⁻¹ *
        (NumV q m (c + 1) (j + 1) / DenV q m (c + 1) (j + 1)
          + (q ^ ((m + 1) * (c + 1)) - 1)⁻¹ * (NumV q m (c + 1) 0 / DenV q m (c + 1) 0))
      = NumV q (m + 1) c j / DenV q (m + 1) c j := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hJ : 0 < Jfac q (m + 1) (j + 1) := Jfac_pos hq _ _
  have hP : 0 < Pfac q m := Pfac_pos hq _
  have hC : 0 < Cfac q m (c + 1) := Cfac_pos hq _ _
  have hm : (0:ℝ) < q ^ (m + 1) - 1 := by have := one_lt_pow_succ hq m; linarith
  have hc : (0:ℝ) < q ^ (c + 1) - 1 := by have := one_lt_pow_succ hq c; linarith
  have hj : (0:ℝ) < q ^ (j + 1) - 1 := by have := one_lt_pow_succ hq j; linarith
  have hmc : (0:ℝ) < q ^ ((m + 1) * (c + 1)) - 1 := by
    have : (1:ℝ) < q ^ ((m + 1) * (c + 1)) := one_lt_pow₀ hq (by positivity)
    linarith
  have hqm : (0:ℝ) < q ^ (m + 1) := pow_pos hq0 _
  have hDen1 : DenV q m (c + 1) (j + 1)
      = Jfac q (m + 1) (j + 1) * Pfac q m * Cfac q m (c + 1) := rfl
  have hDen0 : DenV q m (c + 1) 0
      = (Pfac q m * (q ^ (m + 1) - 1)) * Pfac q m * Cfac q m (c + 1) := by
    unfold DenV
    rw [Jfac_zero_right, Pfac_succ]
  have hDenS : DenV q (m + 1) c j
      = ((q ^ (1 + j) - 1) * Jfac q (m + 1) (j + 1)) * (Pfac q m * (q ^ (m + 1) - 1))
        * ((q ^ (c + 1) - 1) * Cfac q m (c + 1)) := by
    unfold DenV
    rw [Jfac_succ, Pfac_succ, Cfac_succ]
  have hN0 : NumV q m (c + 1) 0 * (q ^ (c + 1) - 1)
      = Pfac q m * (q ^ ((m + 1) * (c + 1)) - 1) := by
    rw [NumV_zero_right]
    have hs : ∑ i ∈ range (m + 1), q ^ ((c + 1) * i) = ∑ i ∈ range (m + 1), (q ^ (c + 1)) ^ i :=
      Finset.sum_congr rfl (fun i _ => by rw [← pow_mul])
    rw [hs, mul_assoc, geom_sum_mul, ← pow_mul, Nat.mul_comm (c + 1) (m + 1)]
  have hrec := NumV_rec (q := q) m c j
  have hjj : q ^ (1 + j) = q ^ (j + 1) := by rw [Nat.add_comm]
  rw [hDen1, hDen0, hDenS, hjj]
  field_simp
  linear_combination (-(Pfac q m * (q ^ ((m + 1) * (c + 1)) - 1))) * hrec
    + Jfac q (m + 1) (j + 1) * hN0

end Positivity

end VolumeAlgebra

end PGLQuotient
-- ==== upstream: Packages/Catalog/Algebra/PGLQuotient/VertexVolumeGeneral.lean ====
/-!
# The vertex volume of the standard arithmetic quotient of `PGL_d`, in arbitrary rank

This file proves the headline computation in **arbitrary rank `d`**: with the Haar measure
normalised so that a maximal compact subgroup has volume `1`, the vertex volume of the standard
nonuniform arithmetic quotient of the affine Bruhat–Tits building of `PGL_d(F_q((t^{-1})))` is

`∑_λ 1/|Aut λ| = d / (P(d) · P(d-1))`,   `P(n) = ∏_{k=1}^{n} (q^k - 1)`

(`vertexVolume_general`, and `vertexVolume_general_rank` for the `d`-indexed form), together
with its `PGL`-normalised variant `(q-1) · ∑_λ 1/|Aut λ|` (`vertexVolume_general_pgl`).

The proof is the promised cut-set recursion, run on the two-parameter twisted mass of
`Algebra.PGLQuotient.TwistedWeight`:

* `twMass_succ`: peeling the top row of a dominant coweight turns the rank-`(n+2)` twisted mass
  into a combination of two rank-`(n+1)` twisted masses (the zero-gap branch and the
  positive-gap branch, the latter summed as a geometric series in the gap);
* `twMass_eq`: solving that recursion by induction on the rank, the closed form being
  `NumV/DenV` from `Algebra.PGLQuotient.VolumeAlgebra`;
* specialising `c = j = 0` gives the vertex volume, since `NumV q n 0 0 = (n+1)·P(n)` and
  `DenV q n 0 0 = P(n+1)·P(n)·P(n)`.

For `d = 2, 3` this recovers `heightZeta_rank_two` (at `s = 0`) and `vertexVolume_rank_three`.
-/

namespace PGLQuotient

open Finset

variable {q : ℝ}

section Summability

/-- The majorant `q^{-P(g)}` of the vertex mass is summable over the dominant sector. -/
lemma summable_inv_pow_pairExp (hq : 1 < q) (n : ℕ) :
    Summable (fun g : Vertex (n + 1) => (q ^ pairExp g)⁻¹) := by
  have hlt : ∀ k : Fin (n + 1 - 1), gapRatio q (n + 1) 0 k < 1 := by
    intro k
    rcases n with _ | m
    · exact k.elim0
    · exact gapRatio_lt_one hq (by omega) (by exact_mod_cast Nat.succ_pos (m + 1)) k
  obtain ⟨hsum, -⟩ := summable_pi_geom (gapRatio q (n + 1) 0) (gapRatio_nonneg hq 0) hlt
  refine hsum.congr (fun g => ?_)
  rw [prod_gapRatio 0 g]
  simp

/-- The twisted vertex mass is summable over the whole quotient. -/
lemma summable_twWeight (hq : 1 < q) (n c j : ℕ) :
    Summable (fun g : Vertex (n + 1) => twWeight q c j g) := by
  refine Summable.of_nonneg_of_le (fun g => (twWeight_pos hq c j g).le) (fun g => ?_)
    ((summable_inv_pow_pairExp hq n).mul_left (((1 - q⁻¹) ^ (n + 1))⁻¹))
  exact le_trans (twWeight_le_vertexWeight hq c j g) (vertexWeight_le g hq)

/-- The vertex mass is summable over the whole quotient. -/
lemma summable_vertexWeight_succ (hq : 1 < q) (n : ℕ) :
    Summable (fun g : Vertex (n + 1) => vertexWeight q g) :=
  (summable_twWeight hq n 0 0).congr (fun g => twWeight_zero_zero g)

end Summability

section Recursion

/-- **The row-peeling recursion for the twisted mass.** -/
theorem twMass_succ (hq : 1 < q) (n c j : ℕ) :
    ∑' g : Vertex (n + 2), twWeight q c j g
      = (q ^ (n + 1) * (q ^ (j + 1) - 1))⁻¹ *
        (∑' g : Vertex (n + 1), twWeight q (c + 1) (j + 1) g
          + (q ^ ((n + 1) * (c + 1)) - 1)⁻¹ * ∑' g : Vertex (n + 1), twWeight q (c + 1) 0 g) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  set K : ℝ := (q ^ (n + 2 + j) * (1 - q⁻¹ ^ (1 + j)))⁻¹ with hKdef
  set M1 : ℝ := ∑' g : Vertex (n + 1), twWeight q (c + 1) (j + 1) g with hM1
  set M0 : ℝ := ∑' g : Vertex (n + 1), twWeight q (c + 1) 0 g with hM0
  have hKval : K = (q ^ (n + 1) * (q ^ (j + 1) - 1))⁻¹ := by
    rw [hKdef]
    congr 1
    have h1 : q ^ (n + 2 + j) = q ^ (n + 1) * q ^ (1 + j) := by
      rw [← pow_add]; congr 1; omega
    have h2 : q ^ (1 + j) = q ^ (j + 1) := by rw [Nat.add_comm]
    rw [h1, inv_pow, h2]
    field_simp
  -- reindex the sum over the top gap
  have hsum2 : Summable (fun g : Vertex (n + 2) => twWeight q c j g) :=
    summable_twWeight hq (n + 1) c j
  have hF : Summable (fun p : ℕ × Vertex (n + 1) => twWeight q c j (consV p.1 p.2)) :=
    (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mpr hsum2
  have hreindex : ∑' g : Vertex (n + 2), twWeight q c j g
      = ∑' p : ℕ × Vertex (n + 1), twWeight q c j (consV p.1 p.2) :=
    ((Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq
      (fun g : Vertex (n + 2) => twWeight q c j g)).symm
  -- the two branches
  have hzero : ∑' g : Vertex (n + 1), twWeight q c j (consV 0 g) = K * M1 := by
    rw [tsum_congr (fun g => twWeight_cons_zero hq c j g), tsum_mul_left]
  have hsucc : ∀ a : ℕ, ∑' g : Vertex (n + 1), twWeight q c j (consV (a + 1) g)
      = K * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * M0 := by
    intro a
    rw [tsum_congr (fun g => twWeight_cons_succ hq c j a g), tsum_mul_left]
  -- the geometric series in the top gap
  have hr0 : (0:ℝ) ≤ (q ^ ((n + 1) * (c + 1)))⁻¹ := by positivity
  have hrlt : (q ^ ((n + 1) * (c + 1)))⁻¹ < 1 := by
    have h1 : (1:ℝ) < q ^ ((n + 1) * (c + 1)) := one_lt_pow₀ hq (by positivity)
    rw [inv_lt_one_iff₀]
    right; exact h1
  have hgeom : ∑' a : ℕ, K * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * M0
      = K * ((q ^ ((n + 1) * (c + 1)) - 1)⁻¹ * M0) := by
    have hterm : ∀ a : ℕ, K * ((q ^ ((n + 1) * (c + 1))) ^ (a + 1))⁻¹ * M0
        = (K * M0 * (q ^ ((n + 1) * (c + 1)))⁻¹) * ((q ^ ((n + 1) * (c + 1)))⁻¹) ^ a := by
      intro a
      rw [← inv_pow, pow_succ]
      ring
    rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hr0 hrlt]
    have hx : (1:ℝ) < q ^ ((n + 1) * (c + 1)) := one_lt_pow₀ hq (by positivity)
    have hxpos : (0:ℝ) < q ^ ((n + 1) * (c + 1)) := by positivity
    field_simp
  rw [hreindex, hF.tsum_prod' (fun a => hF.prod_factor a), Summable.tsum_eq_zero_add hF.prod,
    hzero, tsum_congr hsucc, hgeom, ← hKval]
  ring

/-- **Closed form of the twisted mass in arbitrary rank.** -/
theorem twMass_eq (hq : 1 < q) (n c j : ℕ) :
    ∑' g : Vertex (n + 1), twWeight q c j g = NumV q n c j / DenV q n c j := by
  induction n generalizing c j with
  | zero =>
      have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
      have hval : ∀ g : Vertex 1, twWeight q c j g = (q ^ (1 + j) - 1)⁻¹ := by
        intro g
        have hlam : ∀ i : ℕ, lam g i = 0 := by
          intro i
          unfold lam
          simp
        have hend : endDim g = 1 := by
          unfold endDim
          simp [hlam]
        have hsig : sigmaExp g = 0 := by
          unfold sigmaExp
          simp [hlam]
        have hfb : firstBlockSize g = 1 := by
          unfold firstBlockSize
          simp [hlam]
        have hbr : blockRank g 0 = 1 := by
          unfold blockRank
          simp [hlam, Finset.filter_singleton]
        have hbp : blockProdShift q j g = 1 - q⁻¹ ^ (1 + j) := by
          unfold blockProdShift
          rw [Finset.prod_range_one, hbr, if_pos rfl]
        unfold twWeight
        rw [hend, hsig, hfb, hbp]
        congr 1
        rw [Nat.mul_zero, Nat.add_zero, Nat.mul_one, inv_pow]
        have : q ^ (1 + j) ≠ 0 := by positivity
        field_simp
      have hsub : ∀ b : Vertex 1, b = (fun i => i.elim0) := fun b => funext (fun i => i.elim0)
      rw [tsum_eq_single (fun i => i.elim0) (fun b hb => absurd (hsub b) hb), hval]
      unfold NumV DenV
      simp [Gpoly, Jfac, Pfac, Cfac]
  | succ m ih =>
      rw [twMass_succ hq m c j, ih (c + 1) (j + 1), ih (c + 1) 0, NumDen_step hq]

end Recursion

section Volume

/-- **The vertex volume in arbitrary rank, in closed product form.** -/
theorem vertexVolume_general (hq : 1 < q) (n : ℕ) :
    ∑' g : Vertex (n + 1), vertexWeight q g = (n + 1) / (Pfac q (n + 1) * Pfac q n) := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have h1 : ∑' g : Vertex (n + 1), vertexWeight q g = NumV q n 0 0 / DenV q n 0 0 := by
    rw [← twMass_eq hq n 0 0]
    exact tsum_congr (fun g => (twWeight_zero_zero g).symm)
  have hNum : NumV q n 0 0 = (n + 1) * Pfac q n := by
    rw [NumV_zero_right]
    simp [Finset.sum_const, Finset.card_range]
    ring
  have hDen : DenV q n 0 0 = Pfac q (n + 1) * Pfac q n * Pfac q n := by
    unfold DenV
    rw [Jfac_zero_right]
    congr 1
    unfold Cfac Pfac
    exact Finset.prod_congr rfl (fun k _ => by rw [Nat.zero_add])
  have hP : (0:ℝ) < Pfac q n := Pfac_pos hq n
  have hP1 : (0:ℝ) < Pfac q (n + 1) := Pfac_pos hq (n + 1)
  rw [h1, hNum, hDen]
  field_simp

/-- The vertex volume in arbitrary rank `d ≥ 1`. -/
theorem vertexVolume_general_rank (hq : 1 < q) {d : ℕ} (hd : 1 ≤ d) :
    ∑' g : Vertex d, vertexWeight q g = d / (Pfac q d * Pfac q (d - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  simpa using vertexVolume_general hq n

/-- The `PGL`-normalised vertex volume in arbitrary rank. -/
theorem vertexVolume_general_pgl (hq : 1 < q) (n : ℕ) :
    (q - 1) * ∑' g : Vertex (n + 1), vertexWeight q g
      = (q - 1) * (n + 1) / (Pfac q (n + 1) * Pfac q n) := by
  rw [vertexVolume_general hq n, mul_div_assoc]

end Volume

end PGLQuotient
section
open PGLQuotient
open Finset
variable {q : ℝ}

theorem solution (hq : 1 < q) (n : ℕ) :
    ∑' g : Vertex (n + 1), vertexWeight q g = (n + 1) / (Pfac q (n + 1) * Pfac q n) :=
  PGLQuotient.vertexVolume_general hq n

end
