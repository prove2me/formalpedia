-- Prove2me | solution 1 for UniversalPosets.commonInducedBound_geom
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T21:02:35.207691+00:00
-- url     : https://prove2.me/submissions/ad2c0ecc-be59-4cfb-bb7b-9b32d4e66dd7

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ChainFamily
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_ThreePosetBound

open UniversalPosets in
theorem solution {k i j : ℕ} (hik : i < k) :
    CommonInducedBound (blockChains (4 ^ k) (4 ^ i)) (blockChains (4 ^ k) (4 ^ j))
      (4 ^ (k - i) * 4 ^ j) := by
  classical
  intro A φ hinj hiff
  have ha : 0 < 4 ^ i := by positivity
  have hb : 0 < 4 ^ j := by positivity
  -- split `A` into its blocks of the source order
  have hcard : A.card = ∑ v ∈ A.image (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i),
      (A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem _ hx)
  -- each block lands inside a single block of the target order, so it has at most `4 ^ j` points
  have hfiber : ∀ v ∈ A.image (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i),
      (A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v)).card ≤ 4 ^ j := by
    intro v _
    rcases (A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v)).eq_empty_or_nonempty with hE | ⟨x₀, hx₀⟩
    · rw [hE]
      simp
    · have hmapin : ∀ x ∈ A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v),
          (φ x : ℕ) / 4 ^ j = (φ x₀ : ℕ) / 4 ^ j := by
        intro x hx
        have hxA : x ∈ A := (Finset.mem_filter.1 hx).1
        have hx₀A : x₀ ∈ A := (Finset.mem_filter.1 hx₀).1
        have hblk : (x : ℕ) / 4 ^ i = (x₀ : ℕ) / 4 ^ i := by
          rw [(Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hx₀).2]
        rcases le_total x x₀ with hle | hle
        · exact ((hiff x hxA x₀ hx₀A).1 ⟨hle, hblk⟩).2
        · exact (((hiff x₀ hx₀A x hxA).1 ⟨hle, hblk.symm⟩).2).symm
      have hinj2 : Set.InjOn (fun x : Fin (4 ^ k) => (φ x : ℕ) % 4 ^ j)
          ↑(A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v)) := by
        intro x hx y hy hxy
        have hxF : x ∈ A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v) := hx
        have hyF : y ∈ A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v) := hy
        have hdiv : (φ x : ℕ) / 4 ^ j = (φ y : ℕ) / 4 ^ j := by
          rw [hmapin x hxF, hmapin y hyF]
        have hxy' : (φ x : ℕ) % 4 ^ j = (φ y : ℕ) % 4 ^ j := hxy
        have hnat : (φ x : ℕ) = (φ y : ℕ) := by
          have h1 := Nat.div_add_mod (φ x : ℕ) (4 ^ j)
          have h2 := Nat.div_add_mod (φ y : ℕ) (4 ^ j)
          rw [hdiv, hxy'] at h1
          exact h1.symm.trans h2
        exact hinj (Finset.mem_coe.2 (Finset.mem_filter.1 hxF).1)
          (Finset.mem_coe.2 (Finset.mem_filter.1 hyF).1) (Fin.ext hnat)
      calc (A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v)).card
          = ((A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v)).image
              (fun x : Fin (4 ^ k) => (φ x : ℕ) % 4 ^ j)).card := (Finset.card_image_of_injOn hinj2).symm
        _ ≤ (Finset.range (4 ^ j)).card := by
            refine Finset.card_le_card ?_
            intro z hz
            obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hz
            exact Finset.mem_range.2 (Nat.mod_lt _ hb)
        _ = 4 ^ j := Finset.card_range _
  -- there are at most `4 ^ (k - i)` blocks
  have himg : (A.image (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i)).card ≤ 4 ^ (k - i) := by
    have hsub : A.image (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i) ⊆ Finset.range (4 ^ (k - i)) := by
      intro v hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hv
      refine Finset.mem_range.2 ?_
      have hxN : (x : ℕ) < 4 ^ k := x.isLt
      have hpow : (4 : ℕ) ^ k = 4 ^ (k - i) * 4 ^ i := by
        rw [← pow_add]
        congr 1
        omega
      refine (Nat.div_lt_iff_lt_mul ha).2 ?_
      calc (x : ℕ) < 4 ^ k := hxN
        _ = 4 ^ (k - i) * 4 ^ i := hpow
    calc (A.image (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i)).card ≤ (Finset.range (4 ^ (k - i))).card :=
          Finset.card_le_card hsub
      _ = 4 ^ (k - i) := Finset.card_range _
  calc A.card = ∑ v ∈ A.image (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i),
        (A.filter (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i = v)).card := hcard
    _ ≤ (A.image (fun x : Fin (4 ^ k) => (x : ℕ) / 4 ^ i)).card * 4 ^ j := by
        simpa using Finset.sum_le_card_nsmul _ _ (4 ^ j) hfiber
    _ ≤ 4 ^ (k - i) * 4 ^ j := Nat.mul_le_mul_right _ himg
