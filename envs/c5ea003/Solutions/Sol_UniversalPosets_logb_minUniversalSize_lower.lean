-- Prove2me | solution 1 for UniversalPosets.logb_minUniversalSize_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T23:07:14.913192+00:00
-- url     : https://prove2.me/submissions/0aafd733-63be-4f24-b0ed-669ea8916391

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_Bounds
import Definitions.Def_Cryptography_UniversalPosets_MinSize

set_option maxHeartbeats 1000000 in
open Finset UniversalPosets in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) - 1) / 4 ≤ Real.logb 2 (minUniversalSize n) := by
  classical
  -- ==== UniversalPosets lemmas, proved from the definitions ====
  have host : ∀ n : ℕ, IsUniversalPosetOfSize (2 ^ n) n := by
    intro n
    classical
    have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by simp
    set e : Finset (Fin n) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq hcard with hedef
    refine ⟨fun a b => (e.symm a) ⊆ (e.symm b), ?_, ?_⟩
    · refine { refl := ?_, trans := ?_, antisymm := ?_ }
      · intro a; exact Finset.Subset.refl _
      · intro a b c hab hbc; exact Finset.Subset.trans hab hbc
      · intro a b hab hba
        have : e.symm a = e.symm b := Finset.Subset.antisymm hab hba
        exact e.symm.injective this
    · intro r hr
      haveI := hr
      refine ⟨fun x => e ((univ : Finset (Fin n)).filter (fun z => r z x)), ?_⟩
      intro x y
      simp only [Equiv.symm_apply_apply]
      constructor
      · intro hsub
        have hx : x ∈ (univ : Finset (Fin n)).filter (fun z => r z x) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact refl_of r x
        have := hsub hx
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using this
      · intro hxy z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact trans_of r hz hxy
  -- an `m`-universal host is `n`-universal for every `n ≤ m`
  have restrict : ∀ {N n m : ℕ}, n ≤ m → IsUniversalPosetOfSize N m →
      IsUniversalPosetOfSize N n := by
    intro N n m hnm h
    obtain ⟨H, hH, huniv⟩ := h
    refine ⟨H, hH, ?_⟩
    intro r hr
    haveI := hr
    set i : Fin n → Fin m := fun x => ⟨(x : ℕ), lt_of_lt_of_le x.isLt hnm⟩ with hidef
    have hinj : Function.Injective i := by
      intro a b hab
      apply Fin.ext
      simpa [hidef, Fin.ext_iff] using hab
    set r' : Fin m → Fin m → Prop :=
      fun a b => a = b ∨ ∃ (ha : (a : ℕ) < n) (hb : (b : ℕ) < n), r ⟨a, ha⟩ ⟨b, hb⟩ with hr'def
    have hr'po : IsPartialOrder (Fin m) r' := by
      refine { refl := ?_, trans := ?_, antisymm := ?_ }
      · intro a; exact Or.inl rfl
      · rintro a b c (rfl | ⟨ha, hb, hab⟩) hbc
        · exact hbc
        · rcases hbc with rfl | ⟨hb2, hc, hbc⟩
          · exact Or.inr ⟨ha, hb, hab⟩
          · refine Or.inr ⟨ha, hc, ?_⟩
            have : (⟨b, hb⟩ : Fin n) = ⟨b, hb2⟩ := rfl
            exact trans_of r hab (this ▸ hbc)
      · rintro a b (rfl | ⟨ha, hb, hab⟩) hba
        · rfl
        · rcases hba with rfl | ⟨hb2, ha2, hba⟩
          · rfl
          · have hx : (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ := by
              refine antisymm_of r hab ?_
              have e1 : (⟨b, hb2⟩ : Fin n) = ⟨b, hb⟩ := rfl
              have e2 : (⟨a, ha2⟩ : Fin n) = ⟨a, ha⟩ := rfl
              exact e1 ▸ e2 ▸ hba
            exact Fin.ext (by simpa [Fin.ext_iff] using hx)
    obtain ⟨f, hf⟩ := huniv r' hr'po
    refine ⟨fun x => f (i x), ?_⟩
    intro x y
    rw [hf]
    constructor
    · rintro (heq | ⟨ha, hb, hab⟩)
      · have : x = y := hinj heq
        subst this
        exact refl_of r x
      · exact hab
    · intro hxy
      exact Or.inr ⟨x.isLt, y.isLt, hxy⟩
  have isUniversalPosetOfSize_minUniversalSize : ∀ n : ℕ,
      IsUniversalPosetOfSize (minUniversalSize n) n := by
    intro n
    have hne : ({N | IsUniversalPosetOfSize N n} : Set ℕ).Nonempty := ⟨2 ^ n, host n⟩
    have hmem := Nat.sInf_mem hne
    unfold minUniversalSize
    exact hmem
  have minUniversalSize_mono : Monotone minUniversalSize := by
    intro n m hnm
    have hnem : ({N | IsUniversalPosetOfSize N m} : Set ℕ).Nonempty := ⟨2 ^ m, host m⟩
    have hm : IsUniversalPosetOfSize (minUniversalSize m) m := by
      have hmem := Nat.sInf_mem hnem
      unfold minUniversalSize
      exact hmem
    have hmem2 : minUniversalSize m ∈ {N | IsUniversalPosetOfSize N n} := restrict hnm hm
    unfold minUniversalSize
    exact Nat.sInf_le hmem2
  have two_pow_le_card_sq_of_isUniversalHost : ∀ {U : Type} [LE U] [Fintype U] {m : ℕ},
      1 ≤ m → IsUniversalHost U (Fin (m + m)) → 2 ^ m ≤ (Fintype.card U) ^ 2 := by
    intro U _ _ m hm h
    classical
    set e : Fin m ⊕ Fin m ≃ Fin (m + m) := finSumFinEquiv with hedef
    have hpo : ∀ R : Fin m → Fin m → Prop,
        IsPartialOrder (Fin (m + m)) (fun x y => bipRel R (e.symm x) (e.symm y)) := by
      intro R
      refine { refl := ?_, trans := ?_, antisymm := ?_ }
      · intro a
        rcases hx : e.symm a with b | b <;> simp [bipRel, hx]
      · intro a b c hab hbc
        rcases hxa : e.symm a with x | x <;> rcases hxb : e.symm b with y | y <;>
          rcases hxc : e.symm c with z | z <;>
          rw [hxa, hxb] at hab <;> rw [hxb, hxc] at hbc <;>
          simp only [bipRel] at hab hbc ⊢ <;>
          first
            | exact hab.trans hbc
            | (subst hab; exact hbc)
            | (subst hbc; exact hab)
            | exact hab.elim
            | exact hbc.elim
      · intro a b hab hba
        rcases hxa : e.symm a with x | x <;> rcases hxb : e.symm b with y | y <;>
          rw [hxa, hxb] at hab <;> rw [hxb, hxa] at hba <;>
          simp only [bipRel] at hab hba <;>
          exact e.symm.injective (by rw [hxa, hxb, hab])
    choose f hf using fun (B : Fin m → Fin m → Bool) =>
      h (fun x y => bipRel (fun i j => B i j = true) (e.symm x) (e.symm y))
        (hpo (fun i j => B i j = true))
    set g : (Fin m → Fin m → Bool) → (Fin m → U) × (Fin m → U) :=
      fun B => (fun i => f B (e (Sum.inl i)), fun j => f B (e (Sum.inr j))) with hgdef
    have hginj : Function.Injective g := by
      intro B C hBC
      funext i j
      have h1 : f B (e (Sum.inl i)) = f C (e (Sum.inl i)) :=
        congrFun (congrArg Prod.fst hBC) i
      have h2 : f B (e (Sum.inr j)) = f C (e (Sum.inr j)) :=
        congrFun (congrArg Prod.snd hBC) j
      have hB := hf B (e (Sum.inl i)) (e (Sum.inr j))
      have hC := hf C (e (Sum.inl i)) (e (Sum.inr j))
      simp only [Equiv.symm_apply_apply, bipRel] at hB hC
      rw [h1, h2] at hB
      have hiff : (B i j = true) ↔ (C i j = true) := hB.symm.trans hC
      simpa using hiff
    have hcard := Fintype.card_le_of_injective g hginj
    have hL : Fintype.card (Fin m → Fin m → Bool) = (2 ^ m) ^ m := by
      simp [Fintype.card_fun]
    have hR : Fintype.card ((Fin m → U) × (Fin m → U)) = ((Fintype.card U) ^ 2) ^ m := by
      simp [Fintype.card_fun]
      ring
    rw [hL, hR] at hcard
    exact (Nat.pow_le_pow_iff_left (by omega : m ≠ 0)).mp hcard
  -- ==== end of inlined lemmas ====
  set m : ℕ := n / 2 with hm
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · -- `n = 1`: the left-hand side is zero
    have hn1 : n = 1 := by omega
    subst hn1
    have hnn : (0 : ℝ) ≤ Real.logb 2 (minUniversalSize 1) := by
      rcases Nat.eq_zero_or_pos (minUniversalSize 1) with h0 | hp
      · rw [h0]
        simp
      · refine Real.logb_nonneg (by norm_num) ?_
        exact_mod_cast hp
    norm_num
    exact hnn
  · -- the universal host on `Fin (m + m)` gives the exponential bound
    obtain ⟨H, hH, huniv⟩ := isUniversalPosetOfSize_minUniversalSize (m + m)
    letI : LE (Pt (minUniversalSize (m + m))) := ⟨H⟩
    have hhost : IsUniversalHost (Pt (minUniversalSize (m + m))) (Fin (m + m)) := huniv
    have hcard : Fintype.card (Pt (minUniversalSize (m + m))) = minUniversalSize (m + m) :=
      Fintype.card_fin _
    have hbound := two_pow_le_card_sq_of_isUniversalHost hm1 hhost
    rw [hcard] at hbound
    have hmono : minUniversalSize (m + m) ≤ minUniversalSize n :=
      minUniversalSize_mono (by omega)
    have h2 : (2 : ℕ) ^ m ≤ (minUniversalSize n) ^ 2 :=
      le_trans hbound (Nat.pow_le_pow_left hmono 2)
    have h2m : 2 ≤ (2 : ℕ) ^ m := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    have hUge : 1 ≤ minUniversalSize n := by
      rcases Nat.eq_zero_or_pos (minUniversalSize n) with h0 | hp
      · rw [h0] at h2
        simp at h2
      · exact hp
    have hUR : (1 : ℝ) ≤ (minUniversalSize n : ℝ) := by exact_mod_cast hUge
    have hUpos : (0 : ℝ) < (minUniversalSize n : ℝ) := by linarith
    have hcast : (2 : ℝ) ^ m ≤ ((minUniversalSize n : ℝ)) ^ 2 := by exact_mod_cast h2
    -- take logarithms
    have hlog : (m : ℝ) ≤ 2 * Real.logb 2 (minUniversalSize n) := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have hle : Real.logb 2 ((2 : ℝ) ^ m) ≤ Real.logb 2 ((minUniversalSize n : ℝ) ^ 2) :=
        (Real.logb_le_logb (by norm_num) hpos (by positivity)).mpr hcast
      rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at hle
      push_cast at hle
      linarith
    have hmn : (n : ℝ) - 1 ≤ 2 * (m : ℝ) := by
      have : n ≤ 2 * m + 1 := by omega
      have hc : (n : ℝ) ≤ 2 * (m : ℝ) + 1 := by exact_mod_cast this
      linarith
    linarith
