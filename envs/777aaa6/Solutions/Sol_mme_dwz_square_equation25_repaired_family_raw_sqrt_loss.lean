-- Prove2me | solution 1 for mme_dwz_square_equation25_repaired_family_raw_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:13:52.702572+00:00
-- url     : https://prove2.me/submissions/76fe1843-7be8-4f24-80b9-c1621436218d

import Mathlib.Tactic
import Theorems.Thm_mme_dwz_square_repaired_standard_family_sqrt_loss
import Theorems.Thm_mme_dwz_table2_standard_six_symmetric_component_extraction_sqrt_loss
import Theorems.Thm_mme_dwz_square_componentBase_pos
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_bigAdd_const_isomorphic
import Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((sixSymmetrization
              (TensorObj.kron (CWObj K 6) (CWObj K 6))).kronPow
                (MME.DWZTable2Counts.scale * m)) ∧
          (Real.rpow 2
                (retainedLogRate *
                  ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) *
              (∏ s : Fin 15,
                (componentBase tau s) ^
                  (MME.DWZTable2Counts.component s * m))) ^ (6 : ℕ) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨Csource, hCsource, hsource⟩ :=
    mme_dwz_square_repaired_standard_family_sqrt_loss (K := K)
  obtain ⟨Ccomponent, hCcomponent, hcomponent⟩ :=
    mme_dwz_table2_standard_six_symmetric_component_extraction_sqrt_loss
      (K := K) tau htau
  let C : ℝ := 6 * Csource + Ccomponent
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [hsource, hcomponent] with m hmSource hmComponent
  obtain ⟨sourceCopies, hsourceRestrict, hsourceCount⟩ := hmSource
  obtain ⟨q, A, B, Cdim, hcomponentRestrict, hcomponentWeight⟩ := hmComponent
  let W : ℕ := sourceCopies ^ (6 : ℕ)
  let a : Fin (W * q) → ℕ := fun r =>
    A (finProdFinEquiv.symm r).2
  let b : Fin (W * q) → ℕ := fun r =>
    B (finProdFinEquiv.symm r).2
  let c : Fin (W * q) → ℕ := fun r =>
    Cdim (finProdFinEquiv.symm r).2
  refine ⟨W * q, a, b, c, ?_, ?_⟩
  · let standard := dwzTable2StandardObj K m
    let source := TensorObj.kron (CWObj K 6) (CWObj K 6)
    let extracted := TensorObj.bigAdd
      (fun j : Fin q => MMObj K (A j) (B j) (Cdim j))
    have hsymSource : TensorObj.Restrict
        (sixSymmetrization
          (TensorObj.bigAdd (fun _ : Fin sourceCopies => standard)))
        (sixSymmetrization
          (source.kronPow (MME.DWZTable2Counts.scale * m))) :=
      mme_sixSymmetrization_restrict hsourceRestrict
    have hsourcePower : TensorObj.Restrict
        (sixSymmetrization
          (TensorObj.bigAdd (fun _ : Fin sourceCopies => standard)))
        ((sixSymmetrization source).kronPow
          (MME.DWZTable2Counts.scale * m)) :=
      TensorObj.Restrict.trans hsymSource
        (mme_sixSymmetrization_kronPow_isomorphic source
          (MME.DWZTable2Counts.scale * m)).2
    have hcopies : TensorObj.Restrict
        (TensorObj.bigAdd
          (fun _ : Fin W => sixSymmetrization standard))
        (sixSymmetrization
          (TensorObj.bigAdd (fun _ : Fin sourceCopies => standard))) := by
      dsimp only [W]
      exact (mme_sixSymmetrization_bigAdd_const_isomorphic
        standard sourceCopies).2
    have hreplicated : TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin W => extracted))
        (TensorObj.bigAdd
          (fun _ : Fin W => sixSymmetrization standard)) :=
      mme_bigAdd_mono_restrict (fun _ : Fin W => hcomponentRestrict)
    have hflat : TensorObj.Restrict
        (TensorObj.bigAdd (fun r : Fin (W * q) =>
          MMObj K (a r) (b r) (c r)))
        (TensorObj.bigAdd (fun _ : Fin W => extracted)) := by
      exact (mme_bigAdd_fin_mul_isomorphic_nested
        (fun _ : Fin W => fun j : Fin q =>
          MMObj K (A j) (B j) (Cdim j))).1
    exact TensorObj.Restrict.trans hflat
      (TensorObj.Restrict.trans hreplicated
        (TensorObj.Restrict.trans hcopies hsourcePower))
  · let R : ℝ := Real.rpow 2
        (retainedLogRate *
          ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ))
    let P : ℝ := ∏ s : Fin 15,
      (componentBase tau s) ^
        (MME.DWZTable2Counts.component s * m)
    let s : ℝ := Real.sqrt
      (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
    let S : ℝ := ∑ j : Fin q,
      (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau)
    have hR : 0 < R := by
      dsimp [R]
      positivity
    have hP : 0 < P := by
      dsimp [P]
      apply Finset.prod_pos
      intro i hi
      exact pow_pos (mme_dwz_square_componentBase_pos tau i) _
    have hs : 0 ≤ s := by
      dsimp [s]
      positivity
    have hsourceCount' :
        R * Real.exp (-Csource * s) ≤ (sourceCopies : ℝ) := by
      simpa only [R, s] using hsourceCount
    have hcomponentWeight' :
        P ^ (6 : ℕ) * Real.exp (-Ccomponent * s) ≤ S := by
      simpa only [P, s, S] using hcomponentWeight
    have hsourceSix := pow_le_pow_left₀
      (mul_nonneg hR.le (Real.exp_pos _).le) hsourceCount' 6
    have hexpSix :
        (Real.exp (-Csource * s)) ^ (6 : ℕ) =
          Real.exp (-(6 * Csource) * s) := by
      rw [← Real.exp_nat_mul]
      push_cast
      congr 1
      ring
    have hsourceSix' :
        R ^ (6 : ℕ) * Real.exp (-(6 * Csource) * s) ≤
          (sourceCopies : ℝ) ^ (6 : ℕ) := by
      rw [← hexpSix, ← mul_pow]
      exact hsourceSix
    have hproduct :
        (R ^ (6 : ℕ) * Real.exp (-(6 * Csource) * s)) *
            (P ^ (6 : ℕ) * Real.exp (-Ccomponent * s)) ≤
          (sourceCopies : ℝ) ^ (6 : ℕ) * S := by
      calc
        (R ^ (6 : ℕ) * Real.exp (-(6 * Csource) * s)) *
              (P ^ (6 : ℕ) * Real.exp (-Ccomponent * s))
            ≤ (sourceCopies : ℝ) ^ (6 : ℕ) *
                (P ^ (6 : ℕ) * Real.exp (-Ccomponent * s)) := by
              exact mul_le_mul_of_nonneg_right hsourceSix' (by positivity)
        _ ≤ (sourceCopies : ℝ) ^ (6 : ℕ) * S := by
              exact mul_le_mul_of_nonneg_left hcomponentWeight' (by positivity)
    have hfactor :
        (R * P) ^ (6 : ℕ) * Real.exp (-C * s) =
          (R ^ (6 : ℕ) * Real.exp (-(6 * Csource) * s)) *
            (P ^ (6 : ℕ) * Real.exp (-Ccomponent * s)) := by
      rw [mul_pow]
      rw [show -C * s =
          (-(6 * Csource) * s) + (-Ccomponent * s) by
        dsimp [C]
        ring]
      rw [Real.exp_add]
      ring
    have hsum :
        (W : ℝ) * S =
          ∑ r : Fin (W * q),
            (((a r * b r * c r : ℕ) : ℝ) ^ tau) := by
      calc
        (W : ℝ) * S =
            ∑ p : Fin W × Fin q,
              (((A p.2 * B p.2 * Cdim p.2 : ℕ) : ℝ) ^ tau) := by
                rw [Fintype.sum_prod_type]
                simp only [S, Finset.sum_const, Finset.card_fin]
                rw [nsmul_eq_mul', mul_comm]
        _ = ∑ r : Fin (W * q),
              (((a r * b r * c r : ℕ) : ℝ) ^ tau) := by
                exact (Equiv.sum_comp finProdFinEquiv.symm
                  (fun p : Fin W × Fin q =>
                    (((A p.2 * B p.2 * Cdim p.2 : ℕ) : ℝ) ^ tau))).symm
    change (R * P) ^ (6 : ℕ) * Real.exp (-C * s) ≤
      ∑ r : Fin (W * q), (((a r * b r * c r : ℕ) : ℝ) ^ tau)
    calc
      (R * P) ^ (6 : ℕ) * Real.exp (-C * s)
          = (R ^ (6 : ℕ) * Real.exp (-(6 * Csource) * s)) *
              (P ^ (6 : ℕ) * Real.exp (-Ccomponent * s)) := hfactor
      _ ≤ (sourceCopies : ℝ) ^ (6 : ℕ) * S := hproduct
      _ = (W : ℝ) * S := by
        dsimp [W]
        push_cast
        rfl
      _ = ∑ r : Fin (W * q),
          (((a r * b r * c r : ℕ) : ℝ) ^ tau) := hsum
