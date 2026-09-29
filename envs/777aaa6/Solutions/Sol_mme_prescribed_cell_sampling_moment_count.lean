-- Prove2me | solution 1 for mme_prescribed_cell_sampling_moment_count
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:35:25.847929+00:00
-- url     : https://prove2.me/submissions/7d69d9d8-ff04-4b6e-ad63-7e9cddf5c3ec

import Definitions.Def_mme_recursive_yz_compatibility
import Theorems.Thm_mme_prescribed_cell_query_permutation
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem event_symmetry {P C W J : Type*} [Fintype P] [Fintype W] [Fintype J]
    (cell : P → C) (mu : C → W → ℕ) (q u : J → P)
    (hq : Function.Injective q) (hu : Function.Injective u)
    (hc : ∀ j, cell (q j) = cell (u j)) (w : J → W) :
    Fintype.card {f : {f : P → W // Useful cell mu f} // ∀ j, f.val (q j) = w j} =
    Fintype.card {f : {f : P → W // Useful cell mu f} // ∀ j, f.val (u j) = w j} := by
  classical
  obtain ⟨e,he,heu⟩ := mme_prescribed_cell_query_permutation cell q u hq hu hc
  have hmove (f : P → W) (c : C) (v : W) :
      count cell (fun p ↦ f (e p)) c v = count cell f c v := by
    apply Finset.card_equiv e
    intro p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
  let E : {f : P → W // Useful cell mu f} ≃ {f : P → W // Useful cell mu f} :=
    { toFun := fun f ↦ ⟨fun p ↦ f.val (e p), fun c v ↦ (hmove f.val c v).trans (f.property c v)⟩
      invFun := fun f ↦ ⟨fun p ↦ f.val (e.symm p), by
        intro c v
        have h := hmove (fun p ↦ f.val (e.symm p)) c v
        simp only [Equiv.symm_apply_apply] at h
        exact h.symm.trans (f.property c v)⟩
      left_inv := by intro f; apply Subtype.ext; funext p; exact congrArg f.val (e.apply_symm_apply p)
      right_inv := by intro f; apply Subtype.ext; funext p; exact congrArg f.val (e.symm_apply_apply p) }
  symm
  exact Fintype.card_congr (Equiv.subtypeEquiv E (p := fun f ↦ ∀ j, f.val (u j) = w j)
    (q := fun f ↦ ∀ j, f.val (q j) = w j) (fun f ↦ by
      change (∀ j, f.val (u j) = w j) ↔ (∀ j, f.val (e (q j)) = w j)
      simp only [heu]))

private theorem sample_event_card {P C W J : Type*} [Fintype P] [Fintype J]
    (cell : P → C) (mu : C → W → ℕ) (q : J → P) (w : J → W)
    (f : P → W) (hf : Useful cell mu f) :
    Fintype.card {s : (j : J) → {p : P // cell p = cell (q j)} //
      ∀ j, f (s j).val = w j} = ∏ j, mu (cell (q j)) (w j) := by
  classical
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun j (p : {p : P // cell p = cell (q j)}) ↦ f p.val = w j)), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro j _
  have h : Fintype.card {p : {p : P // cell p = cell (q j)} // f p.val = w j} =
      count cell f (cell (q j)) (w j) := by
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun p ↦ cell p = cell (q j)) (fun p ↦ f p = w j)), Fintype.card_subtype]
    rfl
  exact h.trans (hf _ _)

theorem solution {P C W J : Type*} [Fintype P] [Fintype W] [Fintype J]
    (cell : P → C) (mu : C → W → ℕ) (q : J → P) (hq : Function.Injective q) (w : J → W) :
    let U := {f : P → W // Useful cell mu f}
    let Samples := (j : J) → {p : P // cell p = cell (q j)}
    |(Fintype.card Samples : ℝ) * Fintype.card {f : U // ∀ j, f.val (q j) = w j} -
        (Fintype.card U : ℝ) * ∏ j, (mu (cell (q j)) (w j) : ℝ)| ≤
      (Fintype.card U : ℝ) *
        Fintype.card {s : Samples // ¬ Function.Injective (fun j ↦ (s j).val)} := by
  classical
  let U := {f : P → W // Useful cell mu f}
  let Samples := (j : J) → {p : P // cell p = cell (q j)}
  let A := Fintype.card {f : U // ∀ j, f.val (q j) = w j}
  let B (s : Samples) := Fintype.card {f : U // ∀ j, f.val (s j).val = w j}
  have hswap : ∑ s : Samples, (B s : ℝ) =
      (Fintype.card U : ℝ) * ∏ j, (mu (cell (q j)) (w j) : ℝ) := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset Samples)) (t := (Finset.univ : Finset U))
      (fun s f ↦ ∀ j, f.val (s j).val = w j)
    have hi (f : U) : ((Finset.univ : Finset Samples).filter
        (fun s ↦ ∀ j, f.val (s j).val = w j)).card = ∏ j, mu (cell (q j)) (w j) := by
      simpa only [Fintype.card_subtype] using sample_event_card cell mu q w f.val f.property
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, hi, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] at h
    have hn : ∑ s : Samples, B s = Fintype.card U * ∏ j, mu (cell (q j)) (w j) := by
      simpa only [B, Fintype.card_subtype] using h
    exact_mod_cast hn
  have hA : (A : ℝ) ≤ Fintype.card U := by
    exact_mod_cast Fintype.card_subtype_le (fun f : U ↦ ∀ j, f.val (q j) = w j)
  have hB (s : Samples) : (B s : ℝ) ≤ Fintype.card U := by
    exact_mod_cast Fintype.card_subtype_le (fun f : U ↦ ∀ j, f.val (s j).val = w j)
  have hdiff : (Fintype.card Samples : ℝ) * A -
      (Fintype.card U : ℝ) * ∏ j, (mu (cell (q j)) (w j) : ℝ) =
        ∑ s : Samples, ((A : ℝ) - B s) := by
    rw [Finset.sum_sub_distrib, hswap]
    simp
  change |(Fintype.card Samples : ℝ) * A - _| ≤ _
  rw [hdiff]
  calc
    _ ≤ ∑ s : Samples, |(A : ℝ) - B s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Samples, if Function.Injective (fun j ↦ (s j).val) then (0 : ℝ) else Fintype.card U := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : Function.Injective (fun j ↦ (s j).val)
      · have he : A = B s := event_symmetry cell mu q _ hq hs (fun j ↦ (s j).property.symm) w
        simp [hs, he]
      · simp only [hs, ↓reduceIte]
        apply abs_le.mpr
        constructor <;> nlinarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A,
          show (0 : ℝ) ≤ B s from Nat.cast_nonneg (B s), hB s]
    _ = _ := by
      have hbad : Fintype.card {s : Samples // ¬ Function.Injective (fun j ↦ (s j).val)} =
          ((Finset.univ : Finset Samples).filter (fun s ↦ ¬ Function.Injective (fun j ↦ (s j).val))).card :=
        Fintype.card_subtype _
      rw [hbad]
      have he (s : Samples) :
          (if Function.Injective (fun j ↦ (s j).val) then (0 : ℝ) else Fintype.card U) =
          (if ¬ Function.Injective (fun j ↦ (s j).val) then (Fintype.card U : ℝ) else 0) := by
        by_cases hs : Function.Injective (fun j ↦ (s j).val) <;> simp [hs]
      simp_rw [he]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_comm _ _
