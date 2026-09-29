-- Prove2me | solution 1 for mme_global_CW_counted_stage_realization
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:03:24.513394+00:00
-- url     : https://prove2.me/submissions/7aec5da1-ba1b-4e7c-b83b-86c330313984

import Definitions.Def_mme_global_CW_counted_stage
import Theorems.Thm_mme_global_CW_finite_count_budget
import Theorems.Thm_mme_common_hash_scale_realization
import Theorems.Thm_mme_recursive_x_hash_family_counts
open BigOperators MME MME.RecursiveYZ MME.GlobalCW MME.HashExtraction
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem histogram_pos {C W : Type*} [Fintype C] [Fintype W] (mu : C → W → ℕ) :
    0 < histogramNumber mu := by
  classical
  apply Finset.prod_pos
  intro c hc
  exact Nat.multinomial_pos (s := Finset.univ) (f := mu c)

theorem solution {ell M : ℕ} (D : CountedStage ell M) :
    ∃ E : ExactStage ell M, E.hash.Budget ∧ E.output = D.output ∧
      D.lower ≤ E.hash.lower ∧ E.repairExponent = D.repairExponent := by
  classical
  have hA : D.reference ∈ RecursiveXHash.ambient D.m :=
    (mme_recursive_x_hash_family_counts D.degree D.R D.bounds D.n D.m).1 D.reference_target
  have hden : ∀ j, 0 < D.den j := by
    intro j
    fin_cases j
    · apply Finset.card_pos.mpr
      exact ⟨RecursiveXHash.block 0 D.reference,Finset.mem_image.mpr ⟨D.reference,hA,rfl⟩⟩
    · exact histogram_pos _
    · exact histogram_pos _
  obtain ⟨p,hp,hodd,hgrade,hpLow,hpHigh,hloads,S,hSr,hSf,hSc,hSlower⟩ :=
    mme_common_hash_scale_realization D.degree D.num D.den hden
  let H : HashData := {
    half := D.degree, R := D.R, parent := D.bounds, n := D.n, m := D.m,
    N := D.N, p := p, prime := hp, odd := hodd, grade_lt := hgrade,
    positions := D.hashPositions, labels := S, labels_range := hSr, labels_free := hSf,
    good := fun _ ↦ ∅ }
  have hdegree : 8 * (RecursiveXHash.ambient (n := H.n) H.m).card ≤
      H.p * ((RecursiveXHash.ambient (n := H.n) H.m).image (RecursiveXHash.block 0)).card := hloads 0
  have hload : ∀ i : Fin 2, ∀ a, a ∈ RecursiveXHash.target H.m →
      128 * D.repairScale * ((RecursiveXHash.target (n := H.n) H.m).filter (fun b ↦
        RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (D.mu (yzMode i)) ≤
          H.p * modeNumber (yzMode i) (D.mu (yzMode i)) := by
    intro i a ha
    have hmax : ((RecursiveXHash.target (n := D.n) D.m).filter (fun b ↦
        RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card ≤
        D.fiberMax (yzMode i) := Finset.le_sup (f := fun a ↦
          ((RecursiveXHash.target (n := D.n) D.m).filter (fun b ↦
            RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card) ha
    have hmul := Nat.mul_le_mul_right
      (compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (D.mu (yzMode i)))
      (Nat.mul_le_mul_left (128 * D.repairScale) hmax)
    have hb := hloads (yzMode i)
    fin_cases i <;>
      simpa [CountedStage.num,CountedStage.den,yzMode,yzBoundary,H] using hmul.trans hb
  have h := mme_global_CW_finite_count_budget H D.repairScale D.mu D.mass hdegree hload
  let H' : HashData := { H with good := (fun q ↦ hashUsable H.m H.positions
    (H.labels.image (fun a : ℕ ↦ (a : ZMod H.p))) q D.repairScale D.mu) }
  let E : ExactStage ell M := {
    hash := H', degree_eq := D.degree_eq, L := D.L, positions := D.positions,
    length := D.length, mu := D.mu, boundary := D.boundary,
    reference := D.reference, reference_target := D.reference_target,
    repairScale := D.repairScale, repairExponent := D.repairExponent,
    capacity := D.capacity, good_holes := h.2 }
  refine ⟨E,h.1,rfl,?_,rfl⟩
  exact hSlower (RecursiveXHash.target (n := D.n) D.m).card E.hash.lower
    (Nat.cast_nonneg _) le_rfl
