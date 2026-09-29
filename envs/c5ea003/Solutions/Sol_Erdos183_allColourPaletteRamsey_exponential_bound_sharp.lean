-- Prove2me | solution 1 for Erdos183.allColourPaletteRamsey_exponential_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:31:17.067723+00:00
-- url     : https://prove2.me/submissions/77c68bb6-8ba5-4783-8264-d6fbb65d92b7

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Data.Int.Star
import Theorems.Thm_Erdos183_log_le_paletteLogWidth
import Theorems.Thm_Erdos183_paletteColourCount_mono
import Theorems.Thm_Erdos183_paletteLogWidth_le_two_log
import Theorems.Thm_Erdos183_paletteLogWidth_two_le
import Theorems.Thm_Erdos183_recursivePaletteRamsey_exponential_bound
import Theorems.Thm_Erdos183_stageWidths_succ_le
import Theorems.Thm_Erdos183_triangleRamseyNumber_forces
import Theorems.Thm_Erdos183_two_mul_stage_le_paletteColourCount

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos183

theorem cliqueFree_compRight_embedding {V K K' : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (e : K ↪ K')
    (hC : ∀ colour : K, (C.labelGraph colour).CliqueFree 3) :
    ∀ colour : K', ((C.compRight e).labelGraph colour).CliqueFree 3 := by
  classical
  intro colour T hT
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ :=
    (SimpleGraph.is3Clique_iff).mp hT
  obtain ⟨hxyne, hxycolour⟩ :=
    (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mp hxy
  change e (C.get x y hxyne) = colour at hxycolour
  let old : K := C.get x y hxyne
  have reflect {u v : V}
      (hadj : ((C.compRight e).labelGraph colour).Adj u v) :
      (C.labelGraph old).Adj u v := by
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    change e (C.get u v hne) = colour at hcolour
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨hne, ?_⟩
    exact e.injective (hcolour.trans hxycolour.symm)
  exact hC old {x, y, z}
    ((SimpleGraph.is3Clique_triple_iff).mpr
      ⟨reflect hxy, reflect hxz, reflect hyz⟩)

theorem triangleRamseyNumber_mono {k l : ℕ} (hkl : k ≤ l) :
    triangleRamseyNumber k ≤ triangleRamseyNumber l := by
  apply Nat.sInf_le
  intro C hC
  have hlarge :
      TriangleFree (C.compRight (Fin.castLEEmb hkl)) :=
    cliqueFree_compRight_embedding C (Fin.castLEEmb hkl) hC
  exact triangleRamseyNumber_forces l
    (C.compRight (Fin.castLEEmb hkl)) hlarge

theorem paletteLogWidth_le_stage (H : ℕ) (hH : 2 ≤ H) :
    paletteLogWidth H ≤ H := by
  unfold paletteLogWidth
  apply max_le
  · exact hH
  · apply Nat.ceil_le.mpr
    have hpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    have hlog := Real.log_le_sub_one_of_pos hpos
    exact hlog.trans (by linarith)

theorem exists_paletteStage_bracket (k : ℕ)
    (hk : paletteColourCount 2 ≤ k) :
    ∃ H : ℕ, 2 ≤ H ∧
      paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1) := by
  have hexists : ∃ H : ℕ, k < paletteColourCount H := by
    refine ⟨k + 1, ?_⟩
    have hcount := two_mul_stage_le_paletteColourCount (k + 1)
    omega
  let M : ℕ := Nat.find hexists
  have hM : k < paletteColourCount M := Nat.find_spec hexists
  have hMpos : 1 ≤ M := by
    by_contra hnot
    have hzero : M = 0 := by omega
    simp [hzero, paletteColourCount] at hM
  have hMlarge : 2 < M := by
    by_contra hnot
    have hMtwo : M ≤ 2 := by omega
    have hmono := paletteColourCount_mono hMpos hMtwo
    omega
  refine ⟨M - 1, by omega, ?_, ?_⟩
  · have hminimal :=
      Nat.find_min hexists (show M - 1 < M by omega)
    change ¬ k < paletteColourCount (M - 1) at hminimal
    omega
  · have hsucc : M - 1 + 1 = M := by omega
    simpa [hsucc] using hM

theorem stage_mul_paletteWidth_le_matrixWidth_sharp (H : ℕ) (hH : 3 ≤ H) :
    H * paletteLogWidth H ≤ saturatedMatrixWidth H := by
  have hpalette := paletteLogWidth_le_two_log H hH
  have hmatrix :
      2 * (H : ℝ) * Real.log (H : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    exact Nat.le_ceil _
  have hscaled :=
    mul_le_mul_of_nonneg_left hpalette (show (0 : ℝ) ≤ H by positivity)
  have hreal :
      ((H * paletteLogWidth H : ℕ) : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    push_cast
    calc
      (H : ℝ) * (paletteLogWidth H : ℝ) ≤
          (H : ℝ) * (2 * Real.log (H : ℝ)) := hscaled
      _ = 2 * (H : ℝ) * Real.log (H : ℝ) := by ring
      _ ≤ (saturatedMatrixWidth H : ℝ) := hmatrix
  exact_mod_cast hreal

theorem saturatedMatrixRows_adjacent_scaled_sharp (H : ℕ) (hH : 3 ≤ H) :
    H * saturatedMatrixRows (H + 1) ≤
      (H + 14) * saturatedMatrixRows H := by
  let w := saturatedMatrixWidth H
  let a := paletteLogWidth H
  have ha : 2 ≤ a := by
    simpa [a] using paletteLogWidth_two_le H
  have hwa : H * a ≤ w := by
    simpa [a, w] using stage_mul_paletteWidth_le_matrixWidth_sharp H hH
  have hthreea : 3 * a ≤ w :=
    (Nat.mul_le_mul_right a hH).trans hwa
  have hnext : saturatedMatrixWidth (H + 1) ≤ w + 4 * a := by
    have hwidth := (stageWidths_succ_le H (by omega)).2
    change saturatedMatrixWidth (H + 1) ≤ w + 2 * a + 4 at hwidth
    exact hwidth.trans (by omega)
  have hrows : saturatedMatrixRows (H + 1) ≤
      (w + 4 * a) * (w + 4 * a + 1) + 1 := by
    unfold saturatedMatrixRows
    gcongr
  calc
    H * saturatedMatrixRows (H + 1) ≤
        H * ((w + 4 * a) * (w + 4 * a + 1) + 1) :=
      Nat.mul_le_mul_left H hrows
    _ = H * (w * (w + 1) + 1) +
        H * a * (8 * w + 16 * a + 4) := by ring
    _ ≤ H * (w * (w + 1) + 1) +
        14 * (w * (w + 1) + 1) :=
      Nat.add_le_add_left (by
        calc
          H * a * (8 * w + 16 * a + 4) ≤
              w * (8 * w + 16 * a + 4) :=
            Nat.mul_le_mul_right _ hwa
          _ ≤ w * (14 * w + 4) :=
            Nat.mul_le_mul_left w (by omega)
          _ ≤ 14 * (w * (w + 1) + 1) := by nlinarith) _
    _ = (H + 14) * saturatedMatrixRows H := by
      simp [w, saturatedMatrixRows]
      ring

theorem paletteColourCount_adjacent_scaled_sharp (H : ℕ) (hH : 3 ≤ H) :
    paletteLogWidth H * paletteColourCount (H + 1) ≤
      (paletteLogWidth H + 34) * paletteColourCount H := by
  let a := paletteLogWidth H
  let s := saturatedMatrixRows H
  let s' := saturatedMatrixRows (H + 1)
  have haH : a ≤ H := by
    simpa [a] using paletteLogWidth_le_stage H (by omega)
  have ha' : paletteLogWidth (H + 1) ≤ a + 1 := by
    simpa [a] using (stageWidths_succ_le H (by omega)).1
  have hrows : H * s' ≤ (H + 14) * s := by
    simpa [s, s'] using saturatedMatrixRows_adjacent_scaled_sharp H hH
  have hHreal : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hareal : (a : ℝ) ≤ H := by exact_mod_cast haH
  have hpolyreal :
      ((H : ℝ) + 1) * ((a : ℝ) + 1) * ((H : ℝ) + 14) ≤
        ((a : ℝ) + 34) * (H : ℝ) ^ 2 := by
    nlinarith [
      mul_nonneg (show 0 ≤ 15 * (H : ℝ) + 14 by positivity)
        (sub_nonneg.mpr hareal),
      mul_nonneg (show 0 ≤ (H : ℝ) - 3 by linarith)
        (show 0 ≤ 18 * (H : ℝ) + 25 by positivity)]
  have hpoly :
      (H + 1) * (a + 1) * (H + 14) ≤ (a + 34) * H ^ 2 := by
    exact_mod_cast hpolyreal
  have hstep : (H + 1) * (a + 1) * s' ≤ (a + 34) * H * s := by
    apply Nat.le_of_mul_le_mul_left (c := H) ?_ (by omega)
    calc
      H * ((H + 1) * (a + 1) * s') =
          ((H + 1) * (a + 1)) * (H * s') := by ring
      _ ≤ ((H + 1) * (a + 1)) * ((H + 14) * s) :=
        Nat.mul_le_mul_left _ hrows
      _ = ((H + 1) * (a + 1) * (H + 14)) * s := by ring
      _ ≤ ((a + 34) * H ^ 2) * s :=
        Nat.mul_le_mul_right s hpoly
      _ = H * ((a + 34) * H * s) := by ring
  calc
    paletteLogWidth H * paletteColourCount (H + 1) =
        a * ((H + 1) * paletteLogWidth (H + 1) * s') := by
      simp only [a, s', paletteColourCount]
      ring
    _ ≤ a * ((H + 1) * (a + 1) * s') := by
      gcongr
    _ ≤ a * ((a + 34) * H * s) := Nat.mul_le_mul_left a hstep
    _ = (paletteLogWidth H + 34) * paletteColourCount H := by
      simp only [a, s, paletteColourCount]
      ring

theorem palette_exponential_adjacent_transfer_sharp
    (H a k₀ k : ℕ)
    (hH : 3 ≤ H)
    (hlog : Real.log (H : ℝ) ≤ (a : ℝ))
    (hk₀ : k₀ ≤ k)
    (hratio : a * k ≤ (a + 34) * k₀) :
    ((H : ℝ) / Real.exp 38) ^ k ≤
      ((H : ℝ) / Real.exp 4) ^ k₀ := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have htarget : 0 < ((H : ℝ) / Real.exp 38) ^ k := by positivity
  have hsource : 0 < ((H : ℝ) / Real.exp 4) ^ k₀ := by positivity
  have hratioReal :
      (a : ℝ) * (k : ℝ) ≤
        ((a : ℝ) + 34) * (k₀ : ℝ) := by
    exact_mod_cast hratio
  have hdelta : 0 ≤ (k : ℝ) - (k₀ : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hk₀)
  have hweighted := mul_le_mul_of_nonneg_left hlog hdelta
  apply (Real.log_le_log_iff htarget hsource).mp
  rw [Real.log_pow, Real.log_pow,
    Real.log_div hHpos.ne' (Real.exp_ne_zero 38),
    Real.log_div hHpos.ne' (Real.exp_ne_zero 4),
    Real.log_exp, Real.log_exp]
  nlinarith

end Erdos183

open Erdos183

theorem solution (k : ℕ)
    (hk : paletteColourCount 3 ≤ k) :
    ∃ H : ℕ,
      3 ≤ H ∧
      paletteColourCount H ≤ k ∧
      k < paletteColourCount (H + 1) ∧
      ((H : ℝ) / Real.exp 38) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by
  have htwo : paletteColourCount 2 ≤ paletteColourCount 3 :=
    paletteColourCount_mono (by omega) (by omega)
  obtain ⟨H, hH, hlower, hupper⟩ :=
    exists_paletteStage_bracket k (htwo.trans hk)
  have hthree : 3 ≤ H := by
    by_contra hnot
    have htwoeq : H = 2 := by omega
    subst H
    exact (Nat.not_lt_of_ge hk) (by simpa using hupper)
  have hratio :
      paletteLogWidth H * k ≤
        (paletteLogWidth H + 34) * paletteColourCount H := by
    exact (Nat.mul_le_mul_left (paletteLogWidth H)
      (Nat.le_of_lt hupper)).trans
        (paletteColourCount_adjacent_scaled_sharp H hthree)
  refine ⟨H, hthree, hlower, hupper, ?_⟩
  calc
    ((H : ℝ) / Real.exp 38) ^ k ≤
        ((H : ℝ) / Real.exp 4) ^ paletteColourCount H :=
      palette_exponential_adjacent_transfer_sharp H (paletteLogWidth H)
        (paletteColourCount H) k hthree
        (log_le_paletteLogWidth H) hlower hratio
    _ ≤ (triangleRamseyNumber (paletteColourCount H) : ℝ) :=
      by
        simpa [paletteColourCount] using
          recursivePaletteRamsey_exponential_bound H (paletteLogWidth H)
            (by omega) (paletteLogWidth_two_le H) (log_le_paletteLogWidth H)
    _ ≤ (triangleRamseyNumber k : ℝ) := by
      exact_mod_cast triangleRamseyNumber_mono hlower
