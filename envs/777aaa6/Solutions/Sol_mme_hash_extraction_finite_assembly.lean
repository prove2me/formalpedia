-- Prove2me | solution 1 for mme_hash_extraction_finite_assembly
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T09:03:06.614492+00:00
-- url     : https://prove2.me/submissions/deea0ca8-5c17-43ec-9dc7-c8cd3ecbf9d9

import Definitions.Def_mme_hash_extraction_certificate
import Theorems.Thm_mme_recursive_x_hash_finite_usable_isolation

open BigOperators MME MME.RecursiveXHash MME.HashExtraction
set_option autoImplicit false
universe u

private theorem floor_bound (M H : ℕ) (hH : 0 < H) (L : ℝ) (hL : L ≤ M) :
    L / H - 1 ≤ ((M / H : ℕ) : ℝ) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hrem : ((M % H : ℕ) : ℝ) < H := by exact_mod_cast Nat.mod_lt M hH
  have heq : ((M % H : ℕ) : ℝ) + H * ((M / H : ℕ) : ℝ) = M := by
    exact_mod_cast Nat.mod_add_div M H
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hHr).mpr
  nlinarith

theorem solution {K : Type u} [Field K] (d : Data) (tau : ℝ)
    (hbudget : ∀ j, (d.hash j).Budget) (hsource : d.Realizes K) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((sixSymmetrization (MME.StothersFourth.cwFourthObj K 5)).kronPow d.power) ∧
      d.rate tau ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  classical
  have hselect (j : Fin d.factors) :
      ∃ q I, (d.hash j).Selection q I ∧ (d.hash j).lower ≤ (I.card : ℝ) := by
    let z := d.hash j
    letI : Fact z.p.Prime := ⟨z.prime⟩
    obtain ⟨q,I,hT,hE,hgood,hiso,hsize⟩ :=
      mme_recursive_x_hash_finite_usable_isolation z.half z.R z.parent z.n z.m
        z.odd z.grade_lt z.positions z.labels z.labels_range z.labels_free
        (hbudget j).1 z.good (hbudget j).2
    exact ⟨q,I,⟨hT,hE,hgood,hiso⟩,hsize⟩
  choose q I hselect hsize using hselect
  have hprod : (∏ j, (d.hash j).lower) ≤ ((∏ j, (I j).card : ℕ) : ℝ) := by
    push_cast
    apply Finset.prod_le_prod
    · intro j hj
      unfold HashData.lower
      positivity
    · intro j hj
      exact hsize j
  have hfloor := floor_bound (∏ j, (I j).card) d.repairCopies d.repair_pos
    (∏ j, (d.hash j).lower) hprod
  refine ⟨(∏ j, (I j).card) / d.repairCopies, fun _ ↦ d.a,
    fun _ ↦ d.b, fun _ ↦ d.c, hsource q I hselect hsize, ?_⟩
  simpa [Data.rate] using mul_le_mul_of_nonneg_right hfloor
    (Real.rpow_nonneg (by positivity) tau)
