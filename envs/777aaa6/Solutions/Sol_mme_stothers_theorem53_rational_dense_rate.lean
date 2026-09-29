-- Prove2me | solution 1 for mme_stothers_theorem53_rational_dense_rate
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-10T05:56:42.510212+00:00
-- url     : https://prove2.me/submissions/e856f793-571c-45fd-941e-de46b1cbf18c

import Definitions.Def_mme_stothers_general_outer_profile
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace MME.StothersFourth.Dense

/-- Solve the two stationarity relations for the second and third classes.
On a positive point of `N` this map is the identity. -/
noncomputable def gmap (x : Fin 10 → ℝ) : Fin 10 → ℝ :=
  ![x 0, x 1, x 4 * x 5 * x 9 / (x 7) ^ 2, x 4 * x 6 * x 9 / (x 7 * x 8),
    x 4, x 5, x 6, x 7, x 8, x 9]

theorem gmap_eq_self (b : Fin 10 → ℝ) (hb : InN b) (hpos : ∀ i, 0 < b i) :
    gmap b = b := by
  obtain ⟨-, h2, h3⟩ := hb
  have h7 : (0 : ℝ) < b 7 := hpos 7
  have h8 : (0 : ℝ) < b 8 := hpos 8
  funext i
  fin_cases i <;> simp only [gmap] <;> try rfl
  · show b 4 * b 5 * b 9 / (b 7) ^ 2 = b 2
    field_simp
    linarith [h2]
  · show b 4 * b 6 * b 9 / (b 7 * b 8) = b 3
    field_simp
    linarith [h3]

/-- `gmap` is continuous where the seventh and eighth coordinates do not vanish. -/
theorem gmap_tendsto {ι : Type*} {l : Filter ι}
    (x : ι → (Fin 10 → ℝ)) (y : Fin 10 → ℝ)
    (hx : ∀ i, Tendsto (fun n ↦ x n i) l (𝓝 (y i)))
    (h7 : y 7 ≠ 0) (h8 : y 8 ≠ 0) :
    ∀ i, Tendsto (fun n ↦ gmap (x n) i) l (𝓝 (gmap y i)) := by
  intro i
  fin_cases i
  · simpa only [gmap] using hx 0
  · simpa only [gmap] using hx 1
  · show Tendsto (fun n ↦ x n 4 * x n 5 * x n 9 / (x n 7) ^ 2) l
      (𝓝 (y 4 * y 5 * y 9 / (y 7) ^ 2))
    exact Filter.Tendsto.div (((hx 4).mul (hx 5)).mul (hx 9))
      ((hx 7).pow 2) (pow_ne_zero 2 h7)
  · show Tendsto (fun n ↦ x n 4 * x n 6 * x n 9 / (x n 7 * x n 8)) l
      (𝓝 (y 4 * y 6 * y 9 / (y 7 * y 8)))
    exact Filter.Tendsto.div (((hx 4).mul (hx 6)).mul (hx 9))
      ((hx 7).mul (hx 8)) (mul_ne_zero h7 h8)
  · simpa only [gmap] using hx 4
  · simpa only [gmap] using hx 5
  · simpa only [gmap] using hx 6
  · simpa only [gmap] using hx 7
  · simpa only [gmap] using hx 8
  · simpa only [gmap] using hx 9

/-! ## The integral approximants -/

/-- Ceiling approximants of a positive vector at scale `n`. -/
noncomputable def uu (b : Fin 10 → ℝ) (n : ℕ) (i : Fin 10) : ℕ :=
  ⌈(n : ℝ) * b i⌉₊

theorem uu_pos (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) {n : ℕ} (hn : 0 < n)
    (i : Fin 10) : 0 < uu b n i := by
  have : (0 : ℝ) < (n : ℝ) * b i := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact mul_pos hnR (hb i)
  exact Nat.ceil_pos.mpr this

theorem uu_tendsto (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) (i : Fin 10) :
    Tendsto (fun n : ℕ ↦ (uu b n i : ℝ) / (n : ℝ)) atTop (𝓝 (b i)) := by
  have hlow : ∀ᶠ n : ℕ in atTop, b i ≤ (uu b n i : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [le_div_iff₀ hnR]
    have := Nat.le_ceil ((n : ℝ) * b i)
    simpa only [uu, mul_comm] using this
  have hhigh : ∀ᶠ n : ℕ in atTop,
      (uu b n i : ℝ) / (n : ℝ) ≤ b i + 1 / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [div_le_iff₀ hnR]
    have hle : ((uu b n i : ℕ) : ℝ) ≤ (n : ℝ) * b i + 1 := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) * b i := le_of_lt (mul_pos hnR (hb i))
      exact le_of_lt (by simpa only [uu] using Nat.ceil_lt_add_one h0)
    calc ((uu b n i : ℕ) : ℝ) ≤ (n : ℝ) * b i + 1 := hle
      _ = (b i + 1 / (n : ℝ)) * (n : ℝ) := by field_simp
  have hconst : Tendsto (fun _ : ℕ ↦ b i) atTop (𝓝 (b i)) := tendsto_const_nhds
  have hsum : Tendsto (fun n : ℕ ↦ b i + 1 / (n : ℝ)) atTop (𝓝 (b i)) := by
    simpa using hconst.add tendsto_one_div_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst hsum hlow hhigh

/-- The scaling factor that clears the two binomial relations. -/
noncomputable def AA (b : Fin 10 → ℝ) (n : ℕ) : ℕ :=
  (uu b n 7) ^ 2 * (uu b n 8)

/-- The integral partner profile: eight coordinates are ceiling approximants,
and the second and third are solved from the two stationarity relations. -/
noncomputable def ww (b : Fin 10 → ℝ) (n : ℕ) : Fin 10 → ℕ :=
  ![AA b n * uu b n 0,
    AA b n * uu b n 1,
    uu b n 4 * uu b n 5 * uu b n 9 * uu b n 8,
    uu b n 4 * uu b n 6 * uu b n 9 * uu b n 7,
    AA b n * uu b n 4,
    AA b n * uu b n 5,
    AA b n * uu b n 6,
    AA b n * uu b n 7,
    AA b n * uu b n 8,
    AA b n * uu b n 9]

theorem AA_pos (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) {n : ℕ} (hn : 0 < n) :
    0 < AA b n :=
  Nat.mul_pos (pow_pos (uu_pos b hb hn 7) 2) (uu_pos b hb hn 8)

theorem ww_pos (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) {n : ℕ} (hn : 0 < n)
    (i : Fin 10) : 0 < ww b n i := by
  have hA := AA_pos b hb hn
  have h0 := uu_pos b hb hn 0
  have h1 := uu_pos b hb hn 1
  have h4 := uu_pos b hb hn 4
  have h5 := uu_pos b hb hn 5
  have h6 := uu_pos b hb hn 6
  have h7 := uu_pos b hb hn 7
  have h8 := uu_pos b hb hn 8
  have h9 := uu_pos b hb hn 9
  fin_cases i
  · exact Nat.mul_pos hA h0
  · exact Nat.mul_pos hA h1
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos h4 h5) h9) h8
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos h4 h6) h9) h7
  · exact Nat.mul_pos hA h4
  · exact Nat.mul_pos hA h5
  · exact Nat.mul_pos hA h6
  · exact Nat.mul_pos hA h7
  · exact Nat.mul_pos hA h8
  · exact Nat.mul_pos hA h9

theorem ww_rel2 (b : Fin 10 → ℝ) (n : ℕ) :
    ww b n 2 * (ww b n 7) ^ 2 = ww b n 4 * ww b n 5 * ww b n 9 := by
  show (uu b n 4 * uu b n 5 * uu b n 9 * uu b n 8) * (AA b n * uu b n 7) ^ 2
      = (AA b n * uu b n 4) * (AA b n * uu b n 5) * (AA b n * uu b n 9)
  simp only [AA]
  ring

theorem ww_rel3 (b : Fin 10 → ℝ) (n : ℕ) :
    ww b n 3 * ww b n 7 * ww b n 8 = ww b n 4 * ww b n 6 * ww b n 9 := by
  show (uu b n 4 * uu b n 6 * uu b n 9 * uu b n 7) * (AA b n * uu b n 7) *
      (AA b n * uu b n 8)
      = (AA b n * uu b n 4) * (AA b n * uu b n 6) * (AA b n * uu b n 9)
  simp only [AA]
  ring

theorem ww_ratio (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) {n : ℕ} (hn : 0 < n)
    (i : Fin 10) :
    (ww b n i : ℝ) / ((AA b n : ℝ) * (n : ℝ)) =
      gmap (fun j ↦ (uu b n j : ℝ) / (n : ℝ)) i := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h7 : (0 : ℝ) < ((uu b n 7 : ℕ) : ℝ) := by
    exact_mod_cast uu_pos b hb hn 7
  have h8 : (0 : ℝ) < ((uu b n 8 : ℕ) : ℝ) := by
    exact_mod_cast uu_pos b hb hn 8
  fin_cases i <;>
    simp only [gmap, ww, AA] <;> push_cast <;> field_simp <;> try ring

theorem genProfileScale_ww_pos (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) {n : ℕ}
    (hn : 0 < n) : 0 < genProfileScale (ww b n) := by
  have h0 : 0 < classMultiplicity 0 * ww b n 0 := by
    have hc : classMultiplicity 0 = 1 := by decide
    have := ww_pos b hb hn 0
    rw [hc]; omega
  exact Finset.sum_pos' (fun r _ => Nat.zero_le _) ⟨0, Finset.mem_univ 0, h0⟩

theorem genProfileB_ww_eq (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) {n : ℕ}
    (hn : 0 < n) (i : Fin 10) :
    genProfileB (ww b n) i =
      gmap (fun j ↦ (uu b n j : ℝ) / (n : ℝ)) i /
        ∑ r : Fin 10, (classMultiplicity r : ℝ) *
          gmap (fun j ↦ (uu b n j : ℝ) / (n : ℝ)) r := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hA : (0 : ℝ) < ((AA b n : ℕ) : ℝ) := by exact_mod_cast AA_pos b hb hn
  have hK : (0 : ℝ) < ((AA b n : ℕ) : ℝ) * (n : ℝ) := mul_pos hA hnR
  have hS : (0 : ℝ) < ((genProfileScale (ww b n) : ℕ) : ℝ) := by
    exact_mod_cast genProfileScale_ww_pos b hb hn
  have hnum := ww_ratio b hb hn i
  have hden : ((genProfileScale (ww b n) : ℕ) : ℝ) /
      (((AA b n : ℕ) : ℝ) * (n : ℝ)) =
      ∑ r : Fin 10, (classMultiplicity r : ℝ) *
        gmap (fun j ↦ (uu b n j : ℝ) / (n : ℝ)) r := by
    simp only [genProfileScale]
    push_cast
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [mul_assoc, ← div_eq_mul_inv, ww_ratio b hb hn r]
  rw [← hnum, ← hden]
  simp only [genProfileB]
  field_simp

theorem genProfileB_ww_tendsto (b : Fin 10 → ℝ) (hbInN : InN b)
    (hb : ∀ i, 0 < b i) (i : Fin 10) :
    Tendsto (fun n : ℕ ↦ genProfileB (ww b n) i) atTop (𝓝 (b i)) := by
  have hg0 := gmap_tendsto (fun n : ℕ ↦ fun j ↦ (uu b n j : ℝ) / (n : ℝ)) b
    (fun j ↦ uu_tendsto b hb j) (hb 7).ne' (hb 8).ne'
  have hgb : gmap b = b := gmap_eq_self b hbInN hb
  have hg : ∀ j, Tendsto
      (fun n : ℕ ↦ gmap (fun j ↦ (uu b n j : ℝ) / (n : ℝ)) j) atTop (𝓝 (b j)) := by
    intro j
    have := hg0 j
    rwa [hgb] at this
  have hdenTo : Tendsto
      (fun n : ℕ ↦ ∑ r : Fin 10, (classMultiplicity r : ℝ) *
        gmap (fun j ↦ (uu b n j : ℝ) / (n : ℝ)) r) atTop
      (𝓝 (∑ r : Fin 10, (classMultiplicity r : ℝ) * b r)) :=
    tendsto_finset_sum _ (fun r _ ↦ tendsto_const_nhds.mul (hg r))
  rw [hbInN.1.2] at hdenTo
  have hquot := (hg i).div hdenTo one_ne_zero
  rw [div_one] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (genProfileB_ww_eq b hb hn i).symm

theorem scale_ge (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * b 0 ≤ ((genProfileScale (ww b n) : ℕ) : ℝ) := by
  have hA : 1 ≤ AA b n := AA_pos b hb hn
  have hstep : ww b n 0 ≤ genProfileScale (ww b n) := by
    have hc : classMultiplicity 0 = 1 := by decide
    have hmem : (0 : Fin 10) ∈ (Finset.univ : Finset (Fin 10)) := Finset.mem_univ 0
    have := Finset.single_le_sum
      (f := fun r : Fin 10 ↦ classMultiplicity r * ww b n r)
      (fun r _ ↦ Nat.zero_le _) hmem
    simpa only [hc, one_mul, genProfileScale] using this
  have h1 : (n : ℝ) * b 0 ≤ ((uu b n 0 : ℕ) : ℝ) := by
    simpa only [uu] using Nat.le_ceil ((n : ℝ) * b 0)
  have h2 : ((uu b n 0 : ℕ) : ℝ) ≤ ((ww b n 0 : ℕ) : ℝ) := by
    have : uu b n 0 ≤ ww b n 0 := by
      show uu b n 0 ≤ AA b n * uu b n 0
      exact Nat.le_mul_of_pos_left _ hA
    exact_mod_cast this
  have h3 : ((ww b n 0 : ℕ) : ℝ) ≤ ((genProfileScale (ww b n) : ℕ) : ℝ) := by
    exact_mod_cast hstep
  linarith

theorem scale_tendsto (b : Fin 10 → ℝ) (hb : ∀ i, 0 < b i) :
    Tendsto (fun n : ℕ ↦ ((genProfileScale (ww b n) : ℕ) : ℝ)) atTop atTop := by
  have hlin : Tendsto (fun n : ℕ ↦ (n : ℝ) * b 0) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (hb 0) tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact scale_ge b hb hn

theorem floor_ratio_tendsto {D : ℕ → ℝ} (hD : Tendsto D atTop atTop) (c : ℝ) :
    Tendsto (fun n ↦ ((⌊c * D n⌋ : ℤ) : ℝ) / D n) atTop (𝓝 c) := by
  have hpos : ∀ᶠ n in atTop, 0 < D n := hD.eventually_gt_atTop 0
  have hlow : ∀ᶠ n in atTop, c - 1 / D n ≤ ((⌊c * D n⌋ : ℤ) : ℝ) / D n := by
    filter_upwards [hpos] with n hn
    rw [le_div_iff₀ hn]
    have h := Int.sub_one_lt_floor (c * D n)
    have : (c - 1 / D n) * D n = c * D n - 1 := by field_simp
    rw [this]
    linarith
  have hhigh : ∀ᶠ n in atTop, ((⌊c * D n⌋ : ℤ) : ℝ) / D n ≤ c := by
    filter_upwards [hpos] with n hn
    rw [div_le_iff₀ hn]
    exact Int.floor_le (c * D n)
  have hinv : Tendsto (fun n ↦ 1 / D n) atTop (𝓝 0) := by
    simpa only [one_div] using hD.inv_tendsto_atTop
  have hleft : Tendsto (fun n ↦ c - 1 / D n) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.sub hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft tendsto_const_nhds hlow hhigh

/-- Integer forms of the two displayed kernel vectors. -/
def kSig : Fin 10 → ℤ := ![0, 0, 1, 0, -2, -2, 0, 2, 0, -2]

def kTau : Fin 10 → ℤ := ![0, 0, 0, 1, -2, 0, -1, 1, 2, -2]

theorem kSig_cast (i : Fin 10) : ((kSig i : ℤ) : ℝ) = kernelSigma i := by
  fin_cases i <;> simp [kSig, kernelSigma]

theorem kTau_cast (i : Fin 10) : ((kTau i : ℤ) : ℝ) = kernelTau i := by
  fin_cases i <;> simp [kTau, kernelTau]

theorem kSig_class_sum : (∑ r : Fin 10, (classMultiplicity r : ℤ) * kSig r) = 0 := by
  decide

theorem kTau_class_sum : (∑ r : Fin 10, (classMultiplicity r : ℤ) * kTau r) = 0 := by
  decide

theorem kSig_marg (j : Fin 9) :
    (∑ r : Fin 10, (genClassMarginalMultiplicity r j : ℤ) * kSig r) = 0 := by
  fin_cases j <;> decide

theorem kTau_marg (j : Fin 9) :
    (∑ r : Fin 10, (genClassMarginalMultiplicity r j : ℤ) * kTau r) = 0 := by
  fin_cases j <;> decide

/-- The integral profile obtained by pushing the partner along the kernel. -/
noncomputable def baseZ (b : Fin 10 → ℝ) (s t : ℝ) (n : ℕ) : Fin 10 → ℤ :=
  fun i ↦ (ww b n i : ℤ) +
    ⌊s * ((genProfileScale (ww b n) : ℕ) : ℝ)⌋ * kSig i +
    ⌊t * ((genProfileScale (ww b n) : ℕ) : ℝ)⌋ * kTau i

theorem baseZ_div_tendsto (b : Fin 10 → ℝ) (hbInN : InN b) (hb : ∀ i, 0 < b i)
    (s t : ℝ) (i : Fin 10) :
    Tendsto (fun n : ℕ ↦ (baseZ b s t n i : ℝ) /
        ((genProfileScale (ww b n) : ℕ) : ℝ)) atTop
      (𝓝 (b i + s * kernelSigma i + t * kernelTau i)) := by
  have hD := scale_tendsto b hb
  have hsplit : ∀ n : ℕ,
      (baseZ b s t n i : ℝ) / ((genProfileScale (ww b n) : ℕ) : ℝ) =
        genProfileB (ww b n) i +
          ((⌊s * ((genProfileScale (ww b n) : ℕ) : ℝ)⌋ : ℤ) : ℝ) /
              ((genProfileScale (ww b n) : ℕ) : ℝ) * kernelSigma i +
          ((⌊t * ((genProfileScale (ww b n) : ℕ) : ℝ)⌋ : ℤ) : ℝ) /
              ((genProfileScale (ww b n) : ℕ) : ℝ) * kernelTau i := by
    intro n
    simp only [baseZ, genProfileB]
    push_cast
    rw [← kSig_cast i, ← kTau_cast i]
    ring
  simp only [hsplit]
  have h1 := genProfileB_ww_tendsto b hbInN hb i
  have h2 := (floor_ratio_tendsto hD s).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ kernelSigma i) atTop _)
  have h3 := (floor_ratio_tendsto hD t).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ kernelTau i) atTop _)
  exact (h1.add h2).add h3

theorem baseZ_pos_eventually (b : Fin 10 → ℝ) (hbInN : InN b) (hb : ∀ i, 0 < b i)
    (s t : ℝ)
    (ha : ∀ i, 0 < b i + s * kernelSigma i + t * kernelTau i) :
    ∀ᶠ n : ℕ in atTop, ∀ i, 0 < baseZ b s t n i := by
  have hstep : ∀ i : Fin 10, ∀ᶠ n : ℕ in atTop, 0 < baseZ b s t n i := by
    intro i
    have hlim := baseZ_div_tendsto b hbInN hb s t i
    have hev := hlim.eventually (eventually_gt_nhds (by linarith [ha i] : (0:ℝ) < b i + s * kernelSigma i + t * kernelTau i))
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hS : (0 : ℝ) < ((genProfileScale (ww b n) : ℕ) : ℝ) := by
      exact_mod_cast genProfileScale_ww_pos b hb hn0
    have : (0 : ℝ) < (baseZ b s t n i : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have : (baseZ b s t n i : ℝ) / ((genProfileScale (ww b n) : ℕ) : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hcon hS.le
      linarith
    exact_mod_cast this
  rw [eventually_all]
  exact hstep

noncomputable def bbase (b : Fin 10 → ℝ) (s t : ℝ) (n : ℕ) : Fin 10 → ℕ :=
  fun i ↦ (baseZ b s t n i).toNat

theorem bbase_cast (b : Fin 10 → ℝ) (s t : ℝ) (n : ℕ)
    (h : ∀ i, 0 < baseZ b s t n i) (i : Fin 10) :
    ((bbase b s t n i : ℕ) : ℤ) = baseZ b s t n i :=
  Int.toNat_of_nonneg (h i).le

theorem bbase_pos (b : Fin 10 → ℝ) (s t : ℝ) (n : ℕ)
    (h : ∀ i, 0 < baseZ b s t n i) (i : Fin 10) : 0 < bbase b s t n i := by
  have := bbase_cast b s t n h i
  have hb := h i
  omega

private theorem weighted_sum_baseZ (b : Fin 10 → ℝ) (s t : ℝ) (n : ℕ)
    (c : Fin 10 → ℕ) :
    (∑ r : Fin 10, (c r : ℤ) * baseZ b s t n r) =
      (∑ r : Fin 10, (c r : ℤ) * (ww b n r : ℤ)) +
        (⌊s * ((genProfileScale (ww b n) : ℕ) : ℝ)⌋ *
          ∑ r : Fin 10, (c r : ℤ) * kSig r) +
        (⌊t * ((genProfileScale (ww b n) : ℕ) : ℝ)⌋ *
          ∑ r : Fin 10, (c r : ℤ) * kTau r) := by
  simp only [baseZ, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

theorem scale_bbase (b : Fin 10 → ℝ) (s t : ℝ) (n : ℕ)
    (h : ∀ i, 0 < baseZ b s t n i) :
    genProfileScale (bbase b s t n) = genProfileScale (ww b n) := by
  have hZ : ((genProfileScale (bbase b s t n) : ℕ) : ℤ) =
      ((genProfileScale (ww b n) : ℕ) : ℤ) := by
    simp only [genProfileScale]
    push_cast
    rw [Finset.sum_congr rfl (fun r _ ↦ by rw [bbase_cast b s t n h r])]
    rw [weighted_sum_baseZ b s t n classMultiplicity, kSig_class_sum,
      kTau_class_sum, mul_zero, mul_zero, add_zero, add_zero]
  exact_mod_cast hZ

theorem marg_bbase (b : Fin 10 → ℝ) (s t : ℝ) (n : ℕ)
    (h : ∀ i, 0 < baseZ b s t n i) (j : Fin 9) :
    genMarginalBaseCount (bbase b s t n) j = genMarginalBaseCount (ww b n) j := by
  have hZ : ((genMarginalBaseCount (bbase b s t n) j : ℕ) : ℤ) =
      ((genMarginalBaseCount (ww b n) j : ℕ) : ℤ) := by
    simp only [genMarginalBaseCount]
    push_cast
    rw [Finset.sum_congr rfl (fun r _ ↦ by rw [bbase_cast b s t n h r])]
    rw [weighted_sum_baseZ b s t n (fun r ↦ genClassMarginalMultiplicity r j),
      kSig_marg j, kTau_marg j, mul_zero, mul_zero, add_zero, add_zero]
  exact_mod_cast hZ

theorem genProfileB_bbase (b : Fin 10 → ℝ) (s t : ℝ) (n : ℕ)
    (h : ∀ i, 0 < baseZ b s t n i) (i : Fin 10) :
    genProfileB (bbase b s t n) i =
      (baseZ b s t n i : ℝ) / ((genProfileScale (ww b n) : ℕ) : ℝ) := by
  simp only [genProfileB, scale_bbase b s t n h]
  congr 1
  have := bbase_cast b s t n h i
  exact_mod_cast this

/-- A positive integral vector satisfying the two binomial relations normalises
to a point of `N`. -/
theorem InN_genProfileB (w : Fin 10 → ℕ) (hw : ∀ i, 0 < w i)
    (h2 : w 2 * (w 7) ^ 2 = w 4 * w 5 * w 9)
    (h3 : w 3 * w 7 * w 8 = w 4 * w 6 * w 9) :
    InN (genProfileB w) := by
  have hSpos : 0 < genProfileScale w := by
    have hc : classMultiplicity 0 = 1 := by decide
    exact Finset.sum_pos' (fun r _ => Nat.zero_le _)
      ⟨0, Finset.mem_univ 0, by rw [hc]; have := hw 0; omega⟩
  have hS : (0 : ℝ) < ((genProfileScale w : ℕ) : ℝ) := by exact_mod_cast hSpos
  have hZ : InZ (genProfileB w) := by
    constructor
    · intro i
      exact div_nonneg (Nat.cast_nonneg _) hS.le
    · simp only [genProfileB]
      have hrw : ∀ i : Fin 10,
          (classMultiplicity i : ℝ) * ((w i : ℝ) / ((genProfileScale w : ℕ) : ℝ)) =
            ((classMultiplicity i : ℝ) * (w i : ℝ)) * (((genProfileScale w : ℕ) : ℝ))⁻¹ :=
        fun i ↦ by rw [div_eq_mul_inv]; ring
      rw [Finset.sum_congr rfl (fun i _ ↦ hrw i), ← Finset.sum_mul,
        mul_inv_eq_one₀ hS.ne']
      simp only [genProfileScale]
      push_cast
      rfl
  refine ⟨hZ, ?_, ?_⟩
  · have h2R : ((w 2 : ℕ) : ℝ) * ((w 7 : ℕ) : ℝ) ^ 2 =
        ((w 4 : ℕ) : ℝ) * ((w 5 : ℕ) : ℝ) * ((w 9 : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ ↦ (x : ℝ)) h2
    simp only [genProfileB]
    field_simp
    nlinarith [h2R, hS]
  · have h3R : ((w 3 : ℕ) : ℝ) * ((w 7 : ℕ) : ℝ) * ((w 8 : ℕ) : ℝ) =
        ((w 4 : ℕ) : ℝ) * ((w 6 : ℕ) : ℝ) * ((w 9 : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ ↦ (x : ℝ)) h3
    simp only [genProfileB]
    field_simp
    nlinarith [h3R, hS]

/-! ## Continuity of the rate -/

theorem classValue_pos (tau : ℝ) (i : Fin 10) : 0 < classValue 6 tau i := by
  fin_cases i <;> simp only [classValue, E, H, L] <;> norm_num <;> positivity

theorem Q_tendsto {ι : Type*} {l : Filter ι} (y : ι → (Fin 10 → ℝ))
    (c : Fin 10 → ℝ) (hy : ∀ i, Tendsto (fun n ↦ y n i) l (𝓝 (c i))) (j : Fin 9) :
    Tendsto (fun n ↦ Q (y n) j) l (𝓝 (Q c j)) := by
  have t : ∀ i : Fin 10, Tendsto (fun n ↦ (2 : ℝ) * y n i) l (𝓝 (2 * c i)) :=
    fun i ↦ tendsto_const_nhds.mul (hy i)
  fin_cases j
  · show Tendsto (fun n ↦ 2 * y n 0 + 2 * y n 1 + 2 * y n 2 + 2 * y n 3 + y n 4) l
      (𝓝 (2 * c 0 + 2 * c 1 + 2 * c 2 + 2 * c 3 + c 4))
    exact ((((t 0).add (t 1)).add (t 2)).add (t 3)).add (hy 4)
  · show Tendsto (fun n ↦ 2 * y n 1 + 2 * y n 5 + 2 * y n 6 + 2 * y n 7) l
      (𝓝 (2 * c 1 + 2 * c 5 + 2 * c 6 + 2 * c 7))
    exact (((t 1).add (t 5)).add (t 6)).add (t 7)
  · show Tendsto (fun n ↦ 2 * y n 2 + 2 * y n 6 + 2 * y n 8 + y n 9) l
      (𝓝 (2 * c 2 + 2 * c 6 + 2 * c 8 + c 9))
    exact (((t 2).add (t 6)).add (t 8)).add (hy 9)
  · show Tendsto (fun n ↦ 2 * y n 3 + 2 * y n 7 + 2 * y n 9) l
      (𝓝 (2 * c 3 + 2 * c 7 + 2 * c 9))
    exact ((t 3).add (t 7)).add (t 9)
  · show Tendsto (fun n ↦ 2 * y n 4 + 2 * y n 7 + y n 8) l
      (𝓝 (2 * c 4 + 2 * c 7 + c 8))
    exact ((t 4).add (t 7)).add (hy 8)
  · show Tendsto (fun n ↦ 2 * y n 3 + 2 * y n 6) l (𝓝 (2 * c 3 + 2 * c 6))
    exact (t 3).add (t 6)
  · show Tendsto (fun n ↦ 2 * y n 2 + y n 5) l (𝓝 (2 * c 2 + c 5))
    exact (t 2).add (hy 5)
  · show Tendsto (fun n ↦ 2 * y n 1) l (𝓝 (2 * c 1))
    exact t 1
  · show Tendsto (fun n ↦ y n 0) l (𝓝 (c 0))
    exact hy 0

theorem Q_pos (x : Fin 10 → ℝ) (hx : ∀ i, 0 < x i) (j : Fin 9) : 0 < Q x j := by
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
  have h4 := hx 4; have h5 := hx 5; have h6 := hx 6; have h7 := hx 7
  have h8 := hx 8; have h9 := hx 9
  fin_cases j
  · show 0 < 2 * x 0 + 2 * x 1 + 2 * x 2 + 2 * x 3 + x 4; linarith
  · show 0 < 2 * x 1 + 2 * x 5 + 2 * x 6 + 2 * x 7; linarith
  · show 0 < 2 * x 2 + 2 * x 6 + 2 * x 8 + x 9; linarith
  · show 0 < 2 * x 3 + 2 * x 7 + 2 * x 9; linarith
  · show 0 < 2 * x 4 + 2 * x 7 + x 8; linarith
  · show 0 < 2 * x 3 + 2 * x 6; linarith
  · show 0 < 2 * x 2 + x 5; linarith
  · show 0 < 2 * x 1; linarith
  · show 0 < x 0; linarith

theorem entropyProduct_pos (c : Fin 10 → ℝ) (hc : ∀ i, 0 < c i) :
    0 < entropyProduct c :=
  Finset.prod_pos (fun i _ ↦ Real.rpow_pos_of_pos (hc i) _)

theorem entropyProduct_tendsto {ι : Type*} {l : Filter ι} (y : ι → (Fin 10 → ℝ))
    (c : Fin 10 → ℝ) (hy : ∀ i, Tendsto (fun n ↦ y n i) l (𝓝 (c i)))
    (hc : ∀ i, 0 < c i) :
    Tendsto (fun n ↦ entropyProduct (y n)) l (𝓝 (entropyProduct c)) := by
  simp only [entropyProduct]
  exact tendsto_finset_prod _ (fun i _ ↦
    (hy i).rpow (tendsto_const_nhds.mul (hy i)) (Or.inl (hc i).ne'))

theorem globalRate_tendsto {ι : Type*} {l : Filter ι} (tau : ℝ)
    (y : ι → (Fin 10 → ℝ)) (c : Fin 10 → ℝ)
    (hy : ∀ i, Tendsto (fun n ↦ y n i) l (𝓝 (c i))) (hc : ∀ i, 0 < c i) :
    Tendsto (fun n ↦ globalRate 6 tau (y n) (y n)) l
      (𝓝 (globalRate 6 tau c c)) := by
  simp only [globalRate]
  refine Filter.Tendsto.mul ?_ ?_
  · refine tendsto_finset_prod _ (fun i _ ↦ ?_)
    refine Filter.Tendsto.pow ?_ _
    refine Filter.Tendsto.mul (Filter.Tendsto.mul ?_ ?_) ?_
    · exact tendsto_const_nhds.rpow ((hy i).div_const 3)
        (Or.inl (classValue_pos tau i).ne')
    · exact (hy i).rpow (hy i) (Or.inl (hc i).ne')
    · exact (hy i).rpow (hy i).neg (Or.inl (hc i).ne')
  · refine tendsto_finset_prod _ (fun j _ ↦ ?_)
    have hm : Tendsto (fun n ↦ marginal (y n) j) l (𝓝 (marginal c j)) := by
      simp only [marginal]
      exact (Q_tendsto y c hy j).div_const 3
    have hmpos : 0 < marginal c j := by
      simp only [marginal]
      exact div_pos (Q_pos c hc j) (by norm_num)
    exact hm.rpow hm.neg (Or.inl hmpos.ne')

end MME.StothersFourth.Dense

open MME.StothersFourth.Dense

theorem solution
    (tau : ℝ) (a b : Fin 10 → ℝ)
    (hb : MME.StothersFourth.InN b)
    (haPos : ∀ i, 0 < a i) (hbPos : ∀ i, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i ↦ a i - b i))
    (V : ℝ)
    (hVlt : V < MME.StothersFourth.globalRate 6 tau a a *
      (MME.StothersFourth.entropyProduct b / MME.StothersFourth.entropyProduct a)) :
    ∃ base bstar : Fin 10 → ℕ,
      (∀ r, 0 < base r) ∧ (∀ r, 0 < bstar r) ∧
      (∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
            MME.StothersFourth.genMarginalBaseCount base j) ∧
      MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar) ∧
      V < MME.StothersFourth.globalRate 6 tau
            (MME.StothersFourth.genProfileB base)
            (MME.StothersFourth.genProfileB base) *
          (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB bstar) /
            MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB base)) := by
  obtain ⟨s, t, hst⟩ := hsame
  have haeq : ∀ i, a i = b i + s * MME.StothersFourth.kernelSigma i +
      t * MME.StothersFourth.kernelTau i := by
    intro i
    have := hst i
    linarith
  have haPos' : ∀ i, 0 < b i + s * MME.StothersFourth.kernelSigma i +
      t * MME.StothersFourth.kernelTau i := by
    intro i
    rw [← haeq i]
    exact haPos i
  have hposZ := baseZ_pos_eventually b hb hbPos s t haPos'
  have hT1 : ∀ i, Tendsto (fun n : ℕ ↦
      MME.StothersFourth.genProfileB (ww b n) i) atTop (𝓝 (b i)) :=
    genProfileB_ww_tendsto b hb hbPos
  have hT2 : ∀ i, Tendsto (fun n : ℕ ↦
      MME.StothersFourth.genProfileB (bbase b s t n) i) atTop (𝓝 (a i)) := by
    intro i
    have h := baseZ_div_tendsto b hb hbPos s t i
    rw [← haeq i] at h
    refine h.congr' ?_
    filter_upwards [hposZ] with n hn
    exact (genProfileB_bbase b s t n hn i).symm
  have hEa : (0 : ℝ) < MME.StothersFourth.entropyProduct a := entropyProduct_pos a haPos
  have hrate : Tendsto (fun n : ℕ ↦
      MME.StothersFourth.globalRate 6 tau
          (MME.StothersFourth.genProfileB (bbase b s t n))
          (MME.StothersFourth.genProfileB (bbase b s t n)) *
        (MME.StothersFourth.entropyProduct (MME.StothersFourth.genProfileB (ww b n)) /
          MME.StothersFourth.entropyProduct
            (MME.StothersFourth.genProfileB (bbase b s t n)))) atTop
      (𝓝 (MME.StothersFourth.globalRate 6 tau a a *
        (MME.StothersFourth.entropyProduct b /
          MME.StothersFourth.entropyProduct a))) :=
    (globalRate_tendsto tau _ a hT2 haPos).mul
      ((entropyProduct_tendsto _ b hT1 hbPos).div
        (entropyProduct_tendsto _ a hT2 haPos) hEa.ne')
  have hev := hrate.eventually (eventually_gt_nhds hVlt)
  obtain ⟨n, ⟨hVn, hZn⟩, hn0⟩ :=
    ((hev.and hposZ).and (eventually_gt_atTop 0)).exists
  refine ⟨bbase b s t n, ww b n, bbase_pos b s t n hZn,
    ww_pos b hbPos hn0, ?_, ?_, hVn⟩
  · intro j
    exact (marg_bbase b s t n hZn j).symm
  · exact InN_genProfileB (ww b n) (ww_pos b hbPos hn0)
      (ww_rel2 b n) (ww_rel3 b n)
