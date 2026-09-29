-- Prove2me | solution 2 for Catalog.Probability.SeedRec.card_lfsrWords_le_zero_seed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:48:13.88226+00:00
-- url     : https://prove2.me/submissions/c43910b2-f1d6-49ac-a76b-cf3df26d68e7

import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Definitions.Def_Probability_PRNGEnumerationL1
import Definitions.Def_Probability_PRNGComplexityHierarchy
import Definitions.Def_Probability_PRNGRouterCapacity
import Definitions.Def_Probability_PRNGZeroSeedBound
open Catalog.Probability.SeedRec in
theorem solution {K : Type*} [CommRing K] [Fintype K] [DecidableEq K] (L n : ℕ) :
    (lfsrWords K L n).card ≤ Fintype.card K ^ (2 * L) - Fintype.card K ^ L + 1 := by
  have hstateG : ∀ {L : ℕ} (c σ : Fin L → K) (i : ℕ) (h : i < L) (k : ℕ),
      ((lfsrStep c)^[k] σ) ⟨i, h⟩ = (lfsrPRNG c).stream σ (i + k) := by
    intro L c σ i
    induction i with
    | zero =>
      intro h k
      simp [PRNG.stream, lfsrPRNG, lfsrOut, h]
    | succ i ih =>
      intro h k
      have h' : i < L := by omega
      rw [show i + 1 + k = i + (k + 1) by ring, ← ih h' (k + 1), Function.iterate_succ_apply']
      simp [lfsrStep, h]
  have hltG : ∀ {L : ℕ} (c σ : Fin L → K) (k : ℕ) (h : k < L),
      (lfsrPRNG c).stream σ k = σ ⟨k, h⟩ := by
    intro L c σ k h
    simpa using (hstateG c σ k h 0).symm
  have hrecG : ∀ {L : ℕ}, 0 < L → ∀ (c σ : Fin L → K) (t : ℕ),
      (lfsrPRNG c).stream σ (t + L) = ∑ j : Fin L, c j * (lfsrPRNG c).stream σ (t + (j : ℕ)) := by
    intro L hL c σ t
    have h1 := hstateG c σ (L - 1) (by omega) (t + 1)
    rw [show L - 1 + (t + 1) = t + L by omega, Function.iterate_succ_apply'] at h1
    rw [← h1]
    have hn : ¬ (L - 1 + 1 < L) := by omega
    simp only [lfsrStep, hn, dite_false]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [add_comm t (j : ℕ), ← hstateG c σ j.val j.isLt t]
  have hzeroG : ∀ {L : ℕ} (c : Fin L → K) (t : ℕ), (lfsrPRNG c).stream (fun _ => 0) t = 0 := by
    intro L c t
    have hf : lfsrStep c (fun _ => (0 : K)) = fun _ => (0 : K) := by
      funext i
      simp [lfsrStep]
    simp [PRNG.stream, lfsrPRNG, Function.iterate_fixed hf, lfsrOut]
  classical
  have hlf : lfsrWords K L n =
      Finset.univ.image (fun p : (Fin L → K) × (Fin L → K) => (lfsrPRNG p.1).pref n p.2) := rfl
  have hZcard : (Finset.univ.image (fun c : Fin L → K => (c, (fun _ : Fin L => (0 : K)))) :
      Finset ((Fin L → K) × (Fin L → K))).card = Fintype.card K ^ L := by
    rw [Finset.card_image_of_injective _ (fun c c' h => (Prod.mk.injEq _ _ _ _).mp h |>.1)]
    simp
  have hzw : ∀ p ∈ (Finset.univ.image (fun c : Fin L → K => (c, (fun _ : Fin L => (0 : K)))) :
      Finset ((Fin L → K) × (Fin L → K))), (lfsrPRNG p.1).pref n p.2 = (fun _ : Fin n => (0 : K)) := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨c, rfl⟩ := hp
    funext i
    simpa [PRNG.pref] using hzeroG c i.val
  have hsub : lfsrWords K L n ⊆
      ((Finset.univ \ Finset.univ.image (fun c : Fin L → K => (c, (fun _ : Fin L => (0 : K))))).image
        (fun p : (Fin L → K) × (Fin L → K) => (lfsrPRNG p.1).pref n p.2))
      ∪ {(fun _ : Fin n => (0 : K))} := by
    intro x hx
    rw [hlf] at hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨p, rfl⟩ := hx
    by_cases hp : p ∈ (Finset.univ.image (fun c : Fin L → K => (c, (fun _ : Fin L => (0 : K)))) :
        Finset ((Fin L → K) × (Fin L → K)))
    · rw [hzw p hp]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩)
  calc (lfsrWords K L n).card
      ≤ (((Finset.univ \ Finset.univ.image (fun c : Fin L → K => (c, (fun _ : Fin L => (0 : K))))).image
          (fun p : (Fin L → K) × (Fin L → K) => (lfsrPRNG p.1).pref n p.2))
        ∪ {(fun _ : Fin n => (0 : K))}).card := Finset.card_le_card hsub
    _ ≤ (((Finset.univ \ Finset.univ.image (fun c : Fin L → K => (c, (fun _ : Fin L => (0 : K))))).image
          (fun p : (Fin L → K) × (Fin L → K) => (lfsrPRNG p.1).pref n p.2))).card
        + ({(fun _ : Fin n => (0 : K))} : Finset (Fin n → K)).card := Finset.card_union_le _ _
    _ ≤ (Finset.univ \ Finset.univ.image (fun c : Fin L → K => (c, (fun _ : Fin L => (0 : K))))).card + 1 := by
        simpa using Finset.card_image_le (s := (Finset.univ \ Finset.univ.image
          (fun c : Fin L → K => (c, (fun _ : Fin L => (0 : K)))))) (f := fun p : (Fin L → K) × (Fin L → K) =>
            (lfsrPRNG p.1).pref n p.2)
    _ = Fintype.card K ^ (2 * L) - Fintype.card K ^ L + 1 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hZcard, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_add, two_mul]
