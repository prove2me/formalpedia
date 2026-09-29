-- Prove2me | solution 1 for mme_complete_split_exact_restrictedPower_subexponential_hole_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:32:27.558718+00:00
-- url     : https://prove2.me/submissions/43eba7a0-a070-4210-a631-443241074207

import Theorems.Thm_mme_complete_split_exact_restrictedPower_uniform_basis_interface
import Theorems.Thm_mme_complete_split_exact_type_subexponential_repair_budget
import Theorems.Thm_mme_modern_three_mode_finite_hole_repair
import Definitions.Def_mme_tensor_quotient
import Mathlib.Tactic.Ring
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_modern_three_mode_projected_tensor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.ModernRepair PiTensorProduct Module
open scoped BigOperators Classical

universe u v

set_option autoImplicit false
set_option warningAsError true

private theorem literal_restrict_projected_univ
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (label : ∀ i, I i → Label i) :
    TensorObj.Restrict T (projected T b label (fun _ ↦ Finset.univ)) := by
  have hproj : (fun i ↦ basisLabelProjection (b i) (label i) Finset.univ) =
      (fun i ↦ LinearMap.id (R := K) (M := T.V i)) := by
    funext i
    apply (b i).ext
    intro x
    simp [basisLabelProjection, Basis.constr_basis]
  refine ⟨fun _ ↦ LinearMap.id, ?_⟩
  change PiTensorProduct.map (fun i ↦ LinearMap.id (R := K) (M := T.V i))
    (PiTensorProduct.map
      (fun i ↦ basisLabelProjection (b i) (label i) Finset.univ) T.t) = T.t
  rw [hproj]
  simp only [PiTensorProduct.map_id, LinearMap.id_apply]

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      ∃ h : ℕ, Real.log ((8 ^ h : ℕ) : ℝ) < delta * N ∧
        ∀ beta : Fin 3 → Profile ell,
          let Coord := fun i ↦
            {w : PowIndex (I i) N // ApproxConsistent (label i) (beta i) 0 w}
          let Block := fun i ↦
            {w : PowIndex (CompleteWord ell) N // ApproxConsistent id (beta i) 0 w}
          let S := restrictedPower T b label beta 0 N
          let G := (T.kronPow N).basisAllAllowedGrading
            (fun i ↦ kronPowModeBasis T i (b i) N)
            (fun i ↦ ApproxConsistent (label i) (beta i) 0)
          ∃ B : ∀ i, Basis (Coord i) K (S.V i),
          ∃ blockLabel : ∀ i, Coord i → Block i,
            (∀ i w, (G.classOf i 0).subtype (B i w) =
              kronPowModeBasis T i (b i) N w.1) ∧
            (∀ i w, (blockLabel i w).1 =
              PowIndex.ofFun N (fun r ↦ label i (PowIndex.get N w.1 r))) ∧
            ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (Block i),
              (∀ a i, 8 * N * (holes a i).card ≤ Fintype.card (Block i)) →
              TensorObj.Restrict S
                (TensorObj.bigAdd (fun a ↦
                  projected S B blockLabel (fun i ↦ Finset.univ \ holes a i))) := by
  classical
  intro delta hdelta
  filter_upwards [(mme_complete_split_exact_type_subexponential_repair_budget ell).2
    delta hdelta] with N hN
  obtain ⟨h, hcapacity, hcost⟩ := hN
  refine ⟨h, hcost, ?_⟩
  intro beta
  let S := restrictedPower T b label beta 0 N
  obtain ⟨B, blockLabel, system, hB, hlabel, _hsystem, haction⟩ :=
    mme_complete_split_exact_restrictedPower_uniform_basis_interface T b label beta N
  refine ⟨B, blockLabel, hB, hlabel, ?_⟩
  intro holes hholes
  choose Ψ basisImage ht _hindex hbasis hactionlabel using haction
  have hrepair := mme_modern_three_mode_finite_hole_repair S B blockLabel system
    (fun e i ↦ (Ψ e i).toLinearMap) basisImage hbasis hactionlabel ht
    (2 * N) h (fun _ ↦ Finset.univ) holes
    (by
      intro a i
      convert hholes a i using 1
      ring)
    (by simpa only [Finset.card_univ] using hcapacity beta)
  exact (literal_restrict_projected_univ S B blockLabel).trans hrepair
