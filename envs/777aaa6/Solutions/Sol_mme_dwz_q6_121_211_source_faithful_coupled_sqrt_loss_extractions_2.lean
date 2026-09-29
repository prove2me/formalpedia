-- Prove2me | solution 2 for mme_dwz_q6_121_211_source_faithful_coupled_sqrt_loss_extractions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:07:42.080923+00:00
-- url     : https://prove2.me/submissions/2e0252a2-11c9-42c4-a9b2-a9a0470f56d6

import Mathlib
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_common_halving_bounded
import Theorems.Thm_mme_dwz_q6_121_211_common_halving_family_finite_extraction

open MME BigOperators Filter Topology
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000

private theorem exp_split_two_hundred (C x : ℝ) :
    Real.exp (-(C + 200) * x) =
      Real.exp (-C * x) * Real.exp (-200 * x) := by
  rw [← Real.exp_add]
  congr 1
  ring

private theorem transport_common_halving_family
    {N N' L G A H : ℕ} (hNN' : N = N')
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hHbound : H ≤ 4 ^ N) :
    ∃ family' : CWQ6PrimaryHashFamily N' L G A H,
      ∃ _halving' : family'.CommonBalancedXYHalving,
        H ≤ 4 ^ N' := by
  subst N'
  exact ⟨family, halving, hHbound⟩

private theorem assemble_common_halving_pointwise
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hHbound : H ≤ 4 ^ (MME.DWZTable2Counts.component s * m))
    (hrate :
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component s * m)) *
          Real.exp (-C₀ * Real.sqrt
            ((((MME.DWZTable2Counts.component s * m) + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component s * m)) *
          Real.exp (-(C₀ + 200) * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨q, a, b, c, hrestrict, hextract⟩ :=
    mme_dwz_q6_121_211_common_halving_family_finite_extraction
      (K := K) tau s hs m L G A H family halving hHbound
  refine ⟨q, a, b, c, hrestrict, ?_⟩
  let N : ℕ := MME.DWZTable2Counts.component s * m
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let volume : ℕ := 6 ^ (4 * G + 2 * L)
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let y : ℝ := Real.sqrt
    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
  have hside : side = volume := by
    dsimp [side, volume]
    rw [show (36 : ℕ) = 6 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hsideCube : side * side * side = volume ^ 3 := by
    rw [hside]
    simp [pow_succ]
  have hrateN :
      raw ^ (2 * N) * Real.exp (-C₀ * x) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((volume ^ 3 : ℕ) : ℝ)) ^ tau) := by
    simpa only [raw, N, side, x, hsideCube] using hrate
  have hcombined :
      raw ^ (2 * N) * Real.exp (-(C₀ + 200) * x) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    calc
      raw ^ (2 * N) * Real.exp (-(C₀ + 200) * x) =
          (raw ^ (2 * N) * Real.exp (-C₀ * x)) *
            Real.exp (-200 * x) := by
              rw [exp_split_two_hundred]
              simp only [mul_assoc]
      _ ≤ ((((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
            ((((volume ^ 3 : ℕ) : ℝ)) ^ tau)) *
              Real.exp (-200 * x) :=
            mul_le_mul_of_nonneg_right hrateN (Real.exp_pos _).le
      _ ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
            simpa only [volume, x, N, mul_assoc] using hextract
  have hscomp : MME.DWZTable2Counts.component s = 2073445800000000 := by
    rcases hs with rfl | rfl <;> rfl
  have hNle : N + 1 ≤ MME.DWZTable2Counts.scale * m + 1 := by
    dsimp [N]
    rw [hscomp]
    dsimp [MME.DWZTable2Counts.scale]
    omega
  have hsqrt : x ≤ y := by
    dsimp [x, y]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNle)
  have hexp : Real.exp (-(C₀ + 200) * y) ≤
      Real.exp (-(C₀ + 200) * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  change raw ^ (2 * N) * Real.exp (-(C₀ + 200) * y) ≤ _
  exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans hcombined

private theorem assemble_capacity_at_matching_length
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m N L G A H : ℕ)
    (hNcomp : N = MME.DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hHbound : H ≤ 4 ^ N)
    (hrate :
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component s * m)) *
          Real.exp (-(C₀ + 200) * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨familyS, halvingS, hHboundS⟩ :=
    transport_common_halving_family hNcomp family halving hHbound
  have hrateS :
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component s * m)) *
          Real.exp (-C₀ * Real.sqrt
            ((((MME.DWZTable2Counts.component s * m) + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau) := by
    rw [← hNcomp]
    exact hrate
  exact assemble_common_halving_pointwise
    tau C₀ hC₀ s hs m L G A H familyS halvingS hHboundS hrateS

private def commonHalvingCapacityWitness
    (tau C : ℝ) (N : ℕ) : Prop :=
  let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
  let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  ∃ A H : ℕ,
    ∃ family : CWQ6PrimaryHashFamily N L G A H,
      ∃ _halving : family.CommonBalancedXYHalving,
        H ≤ 4 ^ N ∧
        raw ^ (2 * N) *
            Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
            ((((side * side * side : ℕ) : ℝ)) ^ tau)

private theorem capacityWitness_to_matching_extraction
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m N : ℕ)
    (hNcomp : N = MME.DWZTable2Counts.component s * m)
    (hWitness : commonHalvingCapacityWitness tau C₀ N) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component s * m)) *
          Real.exp (-(C₀ + 200) * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  dsimp only [commonHalvingCapacityWitness] at hWitness
  let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
  let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  change ∃ A H : ℕ,
    ∃ family : CWQ6PrimaryHashFamily N L G A H,
      ∃ _halving : family.CommonBalancedXYHalving,
        H ≤ 4 ^ N ∧
        raw ^ (2 * N) *
            Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
            ((((side * side * side : ℕ) : ℝ)) ^ tau) at hWitness
  obtain ⟨A, H, family, halving, hHbound, hrate⟩ := hWitness
  exact assemble_capacity_at_matching_length
    tau C₀ hC₀ s hs m N L G A H hNcomp family halving hHbound
      (by simpa only [raw, side] using hrate)

private def commonHalvingExtractionGoal
    (K : Type u) [Field K] (tau C : ℝ) (m : ℕ) : Prop :=
  ∀ s : Fin 15, (s = 13 ∨ s = 14) →
    ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd
          (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (4 * (6 : ℝ) ^ (3 * tau) *
          ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component s * m)) *
          Real.exp (-C * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau)

private theorem capacityWitness_to_scaled_extraction
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (m : ℕ)
    (hWitness : commonHalvingCapacityWitness tau C₀
      (2 * (1036722900000000 * m))) :
    commonHalvingExtractionGoal K tau (C₀ + 200) m := by
  dsimp only [commonHalvingExtractionGoal]
  intro s hs
  have hscomp :
      MME.DWZTable2Counts.component s = 2 * 1036722900000000 := by
    rcases hs with rfl | rfl <;> rfl
  have hNcomp : 2 * (1036722900000000 * m) =
      MME.DWZTable2Counts.component s * m := by
    rw [hscomp]
    omega
  exact capacityWitness_to_matching_extraction
    tau C₀ hC₀ s hs m (2 * (1036722900000000 * m)) hNcomp hWitness

private theorem assemble_common_halving_eventually
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hrate : ∀ᶠ n : ℕ in atTop,
      commonHalvingCapacityWitness tau C₀ (2 * n)) :
    ∀ᶠ m : ℕ in atTop,
      commonHalvingExtractionGoal K tau (C₀ + 200) m := by
  let halfCount : ℕ := 1036722900000000
  rw [eventually_atTop] at hrate ⊢
  obtain ⟨n₀, hn₀⟩ := hrate
  refine ⟨n₀, ?_⟩
  intro m hm
  have hscaled : n₀ ≤ halfCount * m := by
    dsimp [halfCount]
    omega
  have hmrate := hn₀ (halfCount * m) hscaled
  exact capacityWitness_to_scaled_extraction tau C₀ hC₀ m hmrate

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 13 ∨ s = 14) →
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd
                (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (4 * (6 : ℝ) ^ (3 * tau) *
                ((6 : ℝ) ^ (3 * tau) + 2)) ^
                  (2 * (MME.DWZTable2Counts.component s * m)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C₀, hC₀, hrate⟩ :=
    mme_CW_q6_primary_hash_sqrt_capacity_common_halving_bounded tau htau
  change ∀ᶠ n : ℕ in atTop,
    commonHalvingCapacityWitness tau C₀ (2 * n) at hrate
  refine ⟨C₀ + 200, by positivity, ?_⟩
  change ∀ᶠ m : ℕ in atTop,
    commonHalvingExtractionGoal K tau (C₀ + 200) m
  exact assemble_common_halving_eventually tau C₀ hC₀ hrate
