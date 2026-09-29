-- Prove2me | solution 2 for SimpleGraph.StarFamily.star_defect_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T03:10:07.661987+00:00
-- url     : https://prove2.me/submissions/7cdfd10c-dec8-4571-b853-28965233d0d0

import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam
import Definitions.Def_Novelty_StarAmalgamThresholdFamily

open Finset SimpleGraph SimpleGraph.StarFamily in
theorem solution {m : ℕ} [NeZero m] :
    (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
        / (Fintype.card (Fin (7 * m + 1)) : ℚ) ≤ (StarK8 m).indepRatio ∧
      (StarK8 m).indepRatio
        = (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
            / (Fintype.card (Fin (7 * m + 1)) : ℚ) := by
  classical
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  -- the extremal set is independent
  have hmaxindep : (StarK8 m).IsIndepSet ↑(maxIndep m) := by
    intro x hx y hy hne hadj
    obtain ⟨-, hcases⟩ := hadj
    simp only [maxIndep, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image,
      Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and] at hx hy
    have hval : ∀ z : Fin (7 * m + 1),
        (z = 0 ∨ ∃ b : Fin m, (⟨7 * b.val + 1, by have := b.isLt; omega⟩ :
          Fin (7 * m + 1)) = z) → z.val = 0 ∨ ∃ c, c < m ∧ z.val = 7 * c + 1 := by
      intro z hz
      rcases hz with rfl | ⟨b, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨b.val, b.isLt, rfl⟩
    have hx' := hval x hx
    have hy' := hval y hy
    rcases hcases with ⟨hx1, hy1, hblk⟩ | ⟨hx0, hy1, hmod⟩ | ⟨hy0, hx1, hmod⟩
    · rcases hx' with hx0 | ⟨c, hc, hxc⟩
      · omega
      · rcases hy' with hy0 | ⟨e, he, hye⟩
        · omega
        · rw [hxc, hye] at hblk
          have hce : c = e := by omega
          exact hne (Fin.ext (by rw [hxc, hye, hce]))
    · rcases hy' with hy0 | ⟨e, he, hye⟩
      · omega
      · rw [hye] at hmod
        omega
    · rcases hx' with hx0 | ⟨c, hc, hxc⟩
      · omega
      · rw [hxc] at hmod
        omega
  have hmaxcard : (maxIndep m).card = m + 1 := by
    have hinj : Function.Injective
        (fun b : Fin m => (⟨7 * b.val + 1, by have := b.isLt; omega⟩ : Fin (7 * m + 1))) := by
      intro a b hab
      have : 7 * a.val + 1 = 7 * b.val + 1 := congrArg Fin.val hab
      exact Fin.ext (by omega)
    have hnot : (0 : Fin (7 * m + 1)) ∉ (Finset.univ : Finset (Fin m)).image
        (fun b => (⟨7 * b.val + 1, by have := b.isLt; omega⟩ : Fin (7 * m + 1))) := by
      intro hmem
      obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hmem
      have : (7 * b.val + 1 : ℕ) = 0 := congrArg Fin.val hb
      omega
    rw [maxIndep, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  -- every independent set has at most `m + 1` vertices
  have hupper : ∀ S : Finset (Fin (7 * m + 1)), (StarK8 m).IsIndepSet ↑S → S.card ≤ m + 1 := by
    intro S hS
    have hinj : Set.InjOn (fun x : Fin (7 * m + 1) => (x.val - 1) / 7) ↑(S.erase 0) := by
      intro x hx y hy hxy
      have hxE : x ∈ S.erase 0 := hx
      have hyE : y ∈ S.erase 0 := hy
      have hx0 : x.val ≠ 0 := by
        intro hv
        apply (Finset.mem_erase.1 hxE).1
        apply Fin.ext
        rw [hv, Fin.val_zero]
      have hy0 : y.val ≠ 0 := by
        intro hv
        apply (Finset.mem_erase.1 hyE).1
        apply Fin.ext
        rw [hv, Fin.val_zero]
      by_contra hne
      have hadj : (StarK8 m).Adj x y :=
        ⟨hne, Or.inl ⟨by omega, by omega, hxy⟩⟩
      exact hS (Finset.mem_coe.2 (Finset.mem_of_mem_erase hxE))
        (Finset.mem_coe.2 (Finset.mem_of_mem_erase hyE)) hne hadj
    have hcard : (S.erase 0).card ≤ m := by
      calc (S.erase 0).card
          = ((S.erase 0).image (fun x : Fin (7 * m + 1) => (x.val - 1) / 7)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range m).card := by
            refine Finset.card_le_card ?_
            intro z hz
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
            have hx0 : x.val ≠ 0 := by
              intro hv
              apply (Finset.mem_erase.1 hx).1
              apply Fin.ext
              rw [hv, Fin.val_zero]
            have := x.isLt
            exact Finset.mem_range.2 (by omega)
        _ = m := Finset.card_range m
    have hpred := Finset.pred_card_le_card_erase (s := S) (a := (0 : Fin (7 * m + 1)))
    omega
  -- hence the independence number is exactly `m + 1`
  have hindepNum : (StarK8 m).indepNum = m + 1 := by
    obtain ⟨S, hS⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := StarK8 m)
    have hle : (StarK8 m).indepNum ≤ m + 1 := by
      have h1 := hupper S hS.isIndepSet
      have h2 := hS.card_eq
      omega
    have hge : m + 1 ≤ (StarK8 m).indepNum := by
      have h3 := hmaxindep.card_le_indepNum
      rw [hmaxcard] at h3
      exact h3
    omega
  -- turn it into the ratio
  have hne : (7 * (m : ℚ) + 1) ≠ 0 := by positivity
  have hsub : ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
    rw [Fintype.card_fin, Nat.cast_sub hm, Nat.cast_one]
  have hratio : (StarK8 m).indepRatio
      = (1 : ℚ) / 4 - ((Fintype.card (Fin m) - 1 : ℕ) : ℚ) * (1 - (1 : ℚ) / 4)
          / (Fintype.card (Fin (7 * m + 1)) : ℚ) := by
    rw [SimpleGraph.indepRatio, hindepNum, hsub, Fintype.card_fin]
    push_cast
    field_simp
    ring
  exact ⟨le_of_eq hratio.symm, hratio⟩
