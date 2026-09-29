-- Prove2me | solution 1 for mme_dwz_table2_equation22_distinct_outer_compatibility_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T15:00:43.842441+00:00
-- url     : https://prove2.me/submissions/b611df72-4a7d-4b18-9c0c-17f774b0e65c

import Mathlib
import Definitions.Def_mme_dwz_table2_split_assignments
import Theorems.Thm_mme_dwz_table2_equation23_numerator_count
import Theorems.Thm_mme_dwz_table2_compatibility_rate_division_free
import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Theorems.Thm_mme_dwz_table2_gamma_pushforward
import Theorems.Thm_mme_finite_indexed_exists_many_compatible_outer_division_free

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

/-- Table-2 Equation-(22) averaging with a literal typical-word denominator
and a conclusion counting distinct compatible outer objects. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    {Outer Position : Type*}
    [Finite Outer] [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (hK : ∀ k,
      Fintype.card {t : Position // K t = k} =
        MME.DWZTable2Counts.alphaZ k * m) :
    let BtypicalK :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    ∀ (assemble :
        (Σ _I : Outer, MME.DWZTable2Cardinality.SplitAssignments m) →
          BtypicalK),
      (∀ I, Function.Injective (fun A => assemble ⟨I, A⟩)) →
      ∃ small : BtypicalK,
        (Nat.card Outer : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ≤
          ((6 * ((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ)) ^ 5 *
            (∏ s : Fin 15,
              if MME.DWZSquare.shapeX s = 0 ∨
                  MME.DWZSquare.shapeY s = 0 then
                (6 *
                  ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3
              else 1) *
            (∏ k : Fin 5,
              (6 *
                ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3)) *
            (Nat.card
              {I : Outer //
                ∃ A : MME.DWZTable2Cardinality.SplitAssignments m,
                  assemble ⟨I, A⟩ = small} : ℝ) := by
  classical
  dsimp only
  intro assemble hinj
  let Assignment := MME.DWZTable2Cardinality.SplitAssignments m
  letI : Finite Assignment := by
    dsimp only [Assignment]
    unfold MME.DWZTable2Cardinality.SplitAssignments
    infer_instance
  let Typical :=
    {small : Position → Fin 3 × Fin 3 //
      (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
      ∀ p, Fintype.card {t : Position // small t = p} =
        MME.DWZTable2Counts.gamma p * m}
  let E : ℝ := Real.exp
    ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
      MME.DWZSquare.logAlphaP)
  let P : ℝ :=
    (6 * ((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ)) ^ 5 *
      (∏ s : Fin 15,
        if MME.DWZSquare.shapeX s = 0 ∨
            MME.DWZSquare.shapeY s = 0 then
          (6 *
            ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3
        else 1) *
      (∏ k : Fin 5,
        (6 * ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3)
  have hPush : ∀ k,
      (∑ p : {p : Fin 3 × Fin 3 //
          MME.DWZTable2Counts.coarseOf p = k},
        MME.DWZTable2Counts.gamma p.1 * m) =
        MME.DWZTable2Counts.alphaZ k * m := by
    intro k
    simpa only [Finset.sum_mul] using congrArg (fun n : ℕ => n * m)
      (mme_dwz_table2_gamma_pushforward k)
  have hCount := mme_dwz_lemma6_7_typical_denominator_count
    MME.DWZTable2Counts.coarseOf K
    (fun p => MME.DWZTable2Counts.gamma p * m)
    (fun k => MME.DWZTable2Counts.alphaZ k * m) hK hPush
  have hTypicalPos : 0 < Nat.card Typical := by
    rw [hCount.1]
    exact Finset.prod_pos fun k hk => Nat.multinomial_pos _ _
  letI : Nonempty Typical := (Nat.card_pos_iff.mp hTypicalPos).1
  obtain ⟨small, havgNat⟩ :=
    mme_finite_indexed_exists_many_compatible_outer_division_free
      (fun _I : Outer => Assignment) assemble (Nat.card Assignment)
      (fun _I => rfl) hinj
  refine ⟨small, ?_⟩
  have hnumReal :
      (Nat.card Assignment : ℝ) =
        (∏ s : Fin 15,
          if MME.DWZSquare.shapeX s = 0 ∨
              MME.DWZSquare.shapeY s = 0 then
            (Nat.multinomial Finset.univ
              (fun r => MME.DWZTable2Counts.split s r * m) : ℝ)
          else 1) *
        ∏ k : Fin 5,
          (Nat.multinomial Finset.univ
            (fun r => MME.DWZTable2Counts.plusSplit k r * m) : ℝ) := by
    dsimp only [Assignment]
    rw [mme_dwz_table2_equation23_numerator_count, Nat.cast_mul]
    simp only [Nat.cast_prod, Nat.cast_ite, Nat.cast_one]
  have hrate := mme_dwz_table2_compatibility_rate_division_free
    m hm (Nat.card Typical) hCount.2
  rw [← hnumReal] at hrate
  have havgReal :
      (Nat.card Outer : ℝ) * (Nat.card Assignment : ℝ) ≤
        (Nat.card Typical : ℝ) *
          (Nat.card
            {I : Outer // ∃ A : Assignment, assemble ⟨I, A⟩ = small} : ℝ) := by
    exact_mod_cast havgNat
  have hB : 0 < (Nat.card Typical : ℝ) := by
    exact_mod_cast hTypicalPos
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  refine le_of_mul_le_mul_left ?_ hB
  change
    (Nat.card Typical : ℝ) * ((Nat.card Outer : ℝ) * E) ≤
      (Nat.card Typical : ℝ) *
        (P *
          (Nat.card
            {I : Outer // ∃ A : Assignment, assemble ⟨I, A⟩ = small} : ℝ))
  calc
    (Nat.card Typical : ℝ) * ((Nat.card Outer : ℝ) * E) =
        (Nat.card Outer : ℝ) * ((Nat.card Typical : ℝ) * E) := by ring
    _ ≤ (Nat.card Outer : ℝ) * (P * (Nat.card Assignment : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [E, P, Typical] using hrate
      · positivity
    _ = P * ((Nat.card Outer : ℝ) * (Nat.card Assignment : ℝ)) := by
      ring
    _ ≤ P *
        ((Nat.card Typical : ℝ) *
          (Nat.card
            {I : Outer // ∃ A : Assignment,
              assemble ⟨I, A⟩ = small} : ℝ)) := by
      exact mul_le_mul_of_nonneg_left havgReal hP
    _ = (Nat.card Typical : ℝ) *
        (P *
          (Nat.card
            {I : Outer // ∃ A : Assignment,
              assemble ⟨I, A⟩ = small} : ℝ)) := by
      ring
