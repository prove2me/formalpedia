-- Prove2me | solution 1 for productFamily_separatesPointsStrongly
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:59:57.830737+00:00
-- url     : https://prove2.me/submissions/3fe8dfca-46a1-466f-984b-7682c6727492

import Mathlib
import Definitions.Def_Bridges_TropicalTensorProductUniversality

open ContinuousMap Set Topology ProductMaxPlusFamily in
theorem solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set C(X, ℝ)} {B : Set C(Y, ℝ)}
    (hA_sep : ∀ x₁ x₂ : X, x₁ ≠ x₂ → ∃ a ∈ A, a x₁ ≠ a x₂)
    (hB_sep : ∀ y₁ y₂ : Y, y₁ ≠ y₂ → ∃ b ∈ B, b y₁ ≠ b y₂) :
    (ProductMaxPlusFamily A B : Set C(X × Y, ℝ)).SeparatesPointsStrongly := by
  -- closure of the family under the max-plus operations, pointwise
  have hconst : ∀ c : ℝ, ∃ k ∈ ProductMaxPlusFamily A B, ∀ p, k p = c :=
    fun c => ⟨_, ProductMaxPlusFamily.const c, fun _ => rfl⟩
  have hmax : ∀ f ∈ ProductMaxPlusFamily A B, ∀ g ∈ ProductMaxPlusFamily A B,
      ∃ k ∈ ProductMaxPlusFamily A B, ∀ p, k p = max (f p) (g p) :=
    fun f hf g hg => ⟨_, ProductMaxPlusFamily.sup hf hg, fun p => rfl⟩
  have hmin : ∀ f ∈ ProductMaxPlusFamily A B, ∀ g ∈ ProductMaxPlusFamily A B,
      ∃ k ∈ ProductMaxPlusFamily A B, ∀ p, k p = min (f p) (g p) := by
    intro f hf g hg
    refine ⟨_, ProductMaxPlusFamily.neg (ProductMaxPlusFamily.sup
      (ProductMaxPlusFamily.neg hf) (ProductMaxPlusFamily.neg hg)), fun p => ?_⟩
    simp only [ContinuousMap.neg_apply, ContinuousMap.sup_apply, max_neg_neg, neg_neg]
  have haff : ∀ f ∈ ProductMaxPlusFamily A B, ∀ (n : ℕ) (c : ℝ),
      ∃ k ∈ ProductMaxPlusFamily A B, ∀ p, k p = n * f p + c := by
    intro f hf n
    induction n with
    | zero =>
      intro c
      obtain ⟨k, hk, hkp⟩ := hconst c
      exact ⟨k, hk, fun p => by rw [hkp]; simp⟩
    | succ n ih =>
      intro c
      obtain ⟨k, hk, hkp⟩ := ih c
      refine ⟨k + f, ProductMaxPlusFamily.add hk hf, fun p => ?_⟩
      rw [ContinuousMap.add_apply, hkp]
      push_cast
      ring
  -- a separating member of the family
  have hsep : ∀ z w : X × Y, z ≠ w → ∃ h ∈ ProductMaxPlusFamily A B, h z ≠ h w := by
    intro z w hzw
    by_cases h1 : z.1 = w.1
    · have h2 : z.2 ≠ w.2 := fun h2 => hzw (Prod.ext h1 h2)
      obtain ⟨b, hb, hbne⟩ := hB_sep _ _ h2
      exact ⟨liftSnd b, ProductMaxPlusFamily.liftB hb, hbne⟩
    · obtain ⟨a, ha, hane⟩ := hA_sep _ _ h1
      exact ⟨liftFst a, ProductMaxPlusFamily.liftA ha, hane⟩
  intro v z w
  by_cases hzw : z = w
  · subst hzw
    obtain ⟨k, hk, hkp⟩ := hconst (v z)
    exact ⟨k, hk, hkp z, hkp z⟩
  -- interpolate along an increasing member `h` (`h z < h w`)
  have key : ∀ h ∈ ProductMaxPlusFamily A B, h z < h w →
      ∃ f ∈ ProductMaxPlusFamily A B, f z = v z ∧ f w = v w := by
    intro h hh hlt
    obtain ⟨n, hn⟩ := exists_nat_gt (|v w - v z| / (h w - h z))
    have hd : 0 < h w - h z := by linarith
    have hn' : |v w - v z| ≤ n * (h w - h z) := by
      rw [div_lt_iff₀ hd] at hn
      linarith
    obtain ⟨g, hg, hgp⟩ := haff h hh n (v z - n * h z)
    have hgz : g z = v z := by rw [hgp]; ring
    have hgw : g w = v z + n * (h w - h z) := by rw [hgp]; ring
    rcases le_total (v z) (v w) with hle | hle
    · -- clamp `g` into `[v z, v w]`
      obtain ⟨k1, hk1, hk1p⟩ := hconst (v z)
      obtain ⟨k2, hk2, hk2p⟩ := hconst (v w)
      obtain ⟨m, hm, hmp⟩ := hmax g hg k1 hk1
      obtain ⟨f, hf, hfp⟩ := hmin m hm k2 hk2
      refine ⟨f, hf, ?_, ?_⟩
      · rw [hfp, hmp, hgz, hk1p, hk2p, max_self, min_eq_left hle]
      · rw [hfp, hmp, hgw, hk1p, hk2p]
        have h3 : v w ≤ v z + n * (h w - h z) := by
          have := le_abs_self (v w - v z)
          linarith
        rw [max_eq_left (by linarith), min_eq_right h3]
    · -- mirror with the decreasing member `2 v z - g`
      obtain ⟨g', hg', hg'p⟩ := haff (-h) (ProductMaxPlusFamily.neg hh) n (v z + n * h z)
      have hg'z : g' z = v z := by
        rw [hg'p, ContinuousMap.neg_apply]
        ring
      have hg'w : g' w = v z - n * (h w - h z) := by
        rw [hg'p, ContinuousMap.neg_apply]
        ring
      obtain ⟨k1, hk1, hk1p⟩ := hconst (v z)
      obtain ⟨k2, hk2, hk2p⟩ := hconst (v w)
      obtain ⟨m, hm, hmp⟩ := hmin g' hg' k1 hk1
      obtain ⟨f, hf, hfp⟩ := hmax m hm k2 hk2
      refine ⟨f, hf, ?_, ?_⟩
      · rw [hfp, hmp, hg'z, hk1p, hk2p, min_self, max_eq_left hle]
      · rw [hfp, hmp, hg'w, hk1p, hk2p]
        have h3 : v z - n * (h w - h z) ≤ v w := by
          have := neg_abs_le (v w - v z)
          linarith
        rw [min_eq_left (by nlinarith [hd, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]),
          max_eq_right h3]
  obtain ⟨h, hh, hne⟩ := hsep z w hzw
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact key h hh hlt
  · exact key (-h) (ProductMaxPlusFamily.neg hh) (by
      simp only [ContinuousMap.neg_apply]
      linarith)
