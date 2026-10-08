-- Prove2me | solution 1 for GoldbachPrincipal_eventual_zero_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:44:23.930432+00:00
-- url     : https://prove2.me/submissions/514e1b25-d580-49c0-80fa-977d1341b07a

import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Complex Set Filter Topology
set_option autoImplicit false

namespace GoldbachPrincipalSupport

private noncomputable def regularized {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : ℂ → ℂ := by
  classical
  exact if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ N
    else DirichletCharacter.LFunction χ

private lemma regularized_differentiable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Differentiable ℂ (regularized χ) := by
  classical
  by_cases hχ : χ = 1
  · simpa [regularized,hχ] using DirichletCharacter.differentiable_LFunctionTrivChar₁ N
  · simpa [regularized,hχ] using DirichletCharacter.differentiable_LFunction hχ

private lemma regularized_one_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : regularized χ 1 ≠ 0 := by
  classical
  by_cases hχ : χ = 1
  · simpa [regularized,hχ] using DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N
  · simpa [regularized,hχ] using DirichletCharacter.LFunction_apply_one_ne_zero hχ

private lemma regularized_zero_iff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    regularized χ s = 0 ↔ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0 := by
  classical
  by_cases hs : s = 1
  · subst s
    simp [regularized_one_ne_zero χ]
  · by_cases hχ : χ = 1
    · simp [regularized,hχ,DirichletCharacter.LFunctionTrivChar₁,
        DirichletCharacter.LFunctionTrivChar,hs,
        mul_eq_zero,sub_ne_zero.mpr hs]
    · simp [regularized,hχ,hs]

private lemma compact_proper_zeros_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (K : Set ℂ) (hK : IsCompact K) :
    (K ∩ {s | s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0}).Finite := by
  have hd := regularized_differentiable χ
  have ha : AnalyticOnNhd ℂ (regularized χ) univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hd
  have hc := ha.preimage_zero_mem_codiscreteWithin
    (regularized_one_ne_zero χ) (mem_univ (1:ℂ)) isConnected_univ
  have hz : IsDiscrete {s | regularized χ s = 0} := by
    simpa using isDiscrete_of_codiscreteWithin hc
  have hclosed : IsClosed {s | regularized χ s = 0} :=
    isClosed_eq hd.continuous continuous_const
  have hf := (hK.inter_right hclosed).finite (hz.mono inter_subset_right)
  simpa only [regularized_zero_iff] using hf

private lemma compact_principal_gap (K : Set ℂ) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, z ∈ K → z ≠ 1 →
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) z = 0 → c ≤ 1-z.re := by
  classical
  let Z := {z : ℂ // z ∈ K ∧ z ≠ 1 ∧
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) z = 0}
  letI : Fintype Z := (compact_proper_zeros_finite (1 : DirichletCharacter ℂ 2) K hK).fintype
  let gap : Z → ℝ := fun z => 1-z.val.re
  have hpos (z : Z) : 0 < gap z := by
    have hre : z.val.re < 1 := by
      by_contra h
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re 1
        (.inr z.property.2.1) (not_lt.mp h)) z.property.2.2
    exact sub_pos.mpr hre
  by_cases hn : (Finset.univ : Finset Z).Nonempty
  · obtain ⟨a,_,hmin⟩ := Finset.exists_min_image Finset.univ gap hn
    refine ⟨gap a,hpos a,?_⟩
    intro z hKz h1 hz
    exact hmin ⟨z,hKz,h1,hz⟩ (Finset.mem_univ _)
  · refine ⟨1,by norm_num,?_⟩
    intro z hKz h1 hz
    exact (hn ⟨⟨z,hKz,h1,hz⟩,Finset.mem_univ _⟩).elim

private lemma principal_euler_factor_ne_zero (p : ℕ) (hp : Nat.Prime p)
    (z : ℂ) (hz : 0 < z.re) : 1-(p:ℂ)^(-z) ≠ 0 := by
  have hnorm : ‖(p:ℂ)^(-z)‖ < 1 := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.pos)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simpa)
  intro h
  have he : (p:ℂ)^(-z) = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hnorm
  exact (lt_irrefl (1:ℝ)) hnorm

private lemma principal_nonzero_of_zeta (N : ℕ) [NeZero N]
    (z : ℂ) (h1 : z ≠ 1) (hz : 0 < z.re) (hζ : riemannZeta z ≠ 0) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) z ≠ 0 := by
  change DirichletCharacter.LFunctionTrivChar N z ≠ 0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h1]
  apply mul_ne_zero _ hζ
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact principal_euler_factor_ne_zero p (Nat.prime_of_mem_primeFactors hp) z hz

-- A qualitative bounded-height strip for zeta. Its width depends on height.
private lemma zeta_bounded_height_zero_free (height : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ ∀ z : ℂ,
      1-δ < z.re → |z.im| ≤ height → riemannZeta z ≠ 0 := by
  let K : Set ℂ := (Icc 0 1) ×ℂ (Icc (-height) height)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨c,hc,hgap⟩ := compact_principal_gap K hK
  let δ : ℝ := min (1/2) c
  have hδ : 0 < δ := lt_min (by norm_num) hc
  refine ⟨δ,hδ,min_le_left _ _,?_⟩
  intro z hre him hz
  have hupper : z.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hδhalf : δ ≤ 1/2 := min_le_left _ _
  have hpos : 0 < z.re := by linarith
  have h1 : z ≠ 1 := by intro h; simp [h] at hupper
  have hzK : z ∈ K := ⟨⟨hpos.le,hupper.le⟩,abs_le.mp him⟩
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2) z = 0 := by
    change DirichletCharacter.LFunctionTrivChar 2 z = 0
    rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h1,hz,mul_zero]
  have hg := hgap z hzK h1 hL
  have hδc : δ ≤ c := min_le_right _ _
  linarith

-- The logarithm cutoff is explicit; the strip width is qualitative.
private lemma principal_zero_exclusion_at_log_cutoff (height : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ ∀ (N : ℕ) [NeZero N],
      1 < N → height < δ*Real.log (N:ℝ) → ∀ z : ℂ,
      z ≠ 1 → (1-z.re)*Real.log (N:ℝ) ≤ height → |z.im| ≤ height →
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) z ≠ 0 := by
  obtain ⟨δ,hδ,hhalf,hstrip⟩ := zeta_bounded_height_zero_free height
  refine ⟨δ,hδ,hhalf,?_⟩
  intro N _ hN hcut z h1 hdef him
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hre : 1-δ < z.re := by nlinarith
  have hpos : 0 < z.re := by linarith
  exact principal_nonzero_of_zeta N z h1 hpos (hstrip z hre him)

end GoldbachPrincipalSupport

theorem solution (height : ℝ) :
    ∃ N₀ : ℕ, 1 < N₀ ∧ ∀ (N : ℕ) [NeZero N], N₀ ≤ N → ∀ z : ℂ,
      z ≠ 1 → (1-z.re)*Real.log (N:ℝ) ≤ height → |z.im| ≤ height →
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) z ≠ 0 := by
  obtain ⟨δ,hδ,_,hcutoff⟩ := GoldbachPrincipalSupport.principal_zero_exclusion_at_log_cutoff height
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (max 1 (Real.exp (height/δ)))
  have hN₀one : 1 < N₀ := by
    exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN₀
  refine ⟨N₀,hN₀one,?_⟩
  intro N _ hN
  have hNone : 1 < N := lt_of_lt_of_le hN₀one hN
  have hpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNreal : (N₀:ℝ) ≤ N := by exact_mod_cast hN
  have hexp : Real.exp (height/δ) < (N:ℝ) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN₀) hNreal
  have hl := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hl
  have hcut : height < δ*Real.log (N:ℝ) := by
    have hc := (div_lt_iff₀ hδ).mp hl
    simpa [mul_comm] using hc
  exact hcutoff N hNone hcut

#print axioms solution
