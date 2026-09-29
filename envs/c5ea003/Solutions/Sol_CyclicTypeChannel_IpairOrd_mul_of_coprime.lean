-- Prove2me | solution 1 for CyclicTypeChannel.IpairOrd_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:21:12.8555+00:00
-- url     : https://prove2.me/submissions/8d538677-526f-4908-bbd0-f54ff15a79ae

-- Sol generated from Shared/CyclicTypeChannelCRTLaw.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
import Theorems.Thm_CyclicTypeChannel_condEnt_comp_injOn
import Theorems.Thm_CyclicTypeChannel_condEnt_cond_injOn
import Theorems.Thm_CyclicTypeChannel_eq_of_mul_eq_mul_coprime
import Theorems.Thm_CyclicTypeChannel_mutInfo_congr
import Theorems.Thm_CyclicTypeChannel_mutInfo_image_injOn
import Theorems.Thm_CyclicTypeChannel_mutInfo_prod
import Theorems.Thm_CyclicTypeChannel_ordType_dvd
import Theorems.Thm_CyclicTypeChannel_ordType_mod
import Theorems.Thm_CyclicTypeChannel_uEnt_comp_injOn
/-
# The CRT additivity law for the splitting-type channel

The exact evaluations show an arithmetic law behind the numbers: for coprime
cyclic orders the type-pair channel is *additive*,

  `I_pair (m * n) = I_pair m + I_pair n`.

This file proves the law in general (for the ordered type pair) from three
ingredients:

* the Chinese Remainder Theorem, which relabels the sample set `CyclicTypeChannel.box (m*n)` as
  the product `CyclicTypeChannel.box m ×ˢ CyclicTypeChannel.box n`;
* the multiplicativity of the splitting type,
  `ord_{mn}(a) = ord_m(a) · ord_n(a)`, together with the fact that this
  factorisation is an *injective recoding* of the pair of component types;
* the additivity of the counting channel over independent products
  (`mutInfo_prod`).

The consequence is a structural explanation of the growth table:
the information of a cyclic order is a sum of primary contributions, so the
one-bit binary cap can be exceeded simply by multiplying orders together.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. The ordered type-pair channel -/




/-! ## 2. Multiplicativity of the splitting type -/

/-- **The splitting type is multiplicative in the order.**  For coprime `m, n`
the type of an exponent in `C_{mn}` is the product of its types in `C_m` and
`C_n`; this is the type-level shadow of `C_{mn} ≅ C_m × C_n`. -/
theorem ordType_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (a : ℕ) :
    ordType (m * n) a = ordType m a * ordType n a := by
  rw [ordType, ordType, ordType, h.gcd_mul a,
    Nat.div_mul_div_comm (Nat.gcd_dvd_right a m) (Nat.gcd_dvd_right a n)]


/-! ## 3. The CRT relabelling of the sample set -/


/-- CRT uniqueness in the form used below. -/
theorem eq_of_mod_eq_mod {m n : ℕ} (h : Nat.Coprime m n) {a b : ℕ} (ha : a < m * n)
    (hb : b < m * n) (h1 : a % m = b % m) (h2 : a % n = b % n) : a = b := by
  have : a ≡ b [MOD m * n] := (Nat.modEq_and_modEq_iff_modEq_mul h).1 ⟨h1, h2⟩
  have := this
  rw [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

theorem crtMap_injOn {m n : ℕ} (h : Nat.Coprime m n) :
    Set.InjOn (crtMap m n) (CyclicTypeChannel.box (m * n)) := by
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' he
  simp only [CyclicTypeChannel.box, coe_product, Set.mem_prod, mem_coe, mem_range] at hab hab'
  simp only [crtMap, Prod.mk.injEq] at he
  obtain ⟨⟨ha1, hb1⟩, ⟨ha2, hb2⟩⟩ := he
  rw [Prod.mk.injEq]
  exact ⟨eq_of_mod_eq_mod h hab.1 hab'.1 ha1 ha2, eq_of_mod_eq_mod h hab.2 hab'.2 hb1 hb2⟩

theorem image_crtMap {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    (CyclicTypeChannel.box (m * n)).image (crtMap m n) = CyclicTypeChannel.box m ×ˢ CyclicTypeChannel.box n := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hx
    simp only [CyclicTypeChannel.box, mem_product, mem_range] at hab ⊢
    exact ⟨⟨Nat.mod_lt _ hm, Nat.mod_lt _ hm⟩, ⟨Nat.mod_lt _ hn, Nat.mod_lt _ hn⟩⟩
  · rw [Finset.card_image_of_injOn (crtMap_injOn h)]
    simp only [CyclicTypeChannel.box, card_product, card_range]
    exact le_of_eq (by ring)

/-! ## 4. The additivity law -/


/-! ## 5. From the ordered to the unordered pair -/




/-! ## 6. The channel is determined by its prime-power values -/




open CyclicTypeChannel in
theorem solution{m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    IpairOrd (m * n) = IpairOrd m + IpairOrd n := by
  classical
  -- the coordinatewise read-out and conditioning variable on the product
  set G : ((ℕ × ℕ) × (ℕ × ℕ)) → (ℕ × ℕ) × (ℕ × ℕ) := fun X => (ordPair m X.1, ordPair n X.2)
    with hG
  set K : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ × ℕ := fun X => (prodRes m X.1, prodRes n X.2) with hK
  -- the multiplicative recoding of a pair of component types
  set f : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ × ℕ := fun z => (z.1.1 * z.2.1, z.1.2 * z.2.2) with hf
  -- the residue-splitting recoding of the product residue
  set d : ℕ → ℕ × ℕ := fun z => (z % m, z % n) with hd
  have hbm : (CyclicTypeChannel.box m).Nonempty := ⟨(0, 0), by simp [CyclicTypeChannel.box, mem_product, hm]⟩
  have hbn : (CyclicTypeChannel.box n).Nonempty := ⟨(0, 0), by simp [CyclicTypeChannel.box, mem_product, hn]⟩
  -- step 1 : the `m*n` read-out is the multiplicative recoding of the CRT read-out
  have hstep1 : ∀ p ∈ CyclicTypeChannel.box (m * n), ordPair (m * n) p = (f ∘ (G ∘ crtMap m n)) p := by
    intro p _
    simp only [hf, hG, crtMap, Function.comp_apply, ordPair, Prod.mk.injEq]
    constructor
    · rw [ordType_mul_of_coprime h, ordType_mod, ordType_mod]
    · rw [ordType_mul_of_coprime h, ordType_mod, ordType_mod]
  have hstep2 : ∀ p ∈ CyclicTypeChannel.box (m * n), (d ∘ prodRes (m * n)) p = (K ∘ crtMap m n) p := by
    intro p _
    simp only [hd, hK, crtMap, Function.comp_apply, prodRes, Prod.mk.injEq]
    constructor
    · rw [Nat.mod_mod_of_dvd _ ⟨n, rfl⟩, Nat.add_mod]
    · rw [Nat.mod_mod_of_dvd _ ⟨m, mul_comm m n⟩, Nat.add_mod]
  -- step 3 : the multiplicative recoding is injective on the values that occur
  have hfinj : Set.InjOn f ((G ∘ crtMap m n) '' (CyclicTypeChannel.box (m * n))) := by
    rintro z hz z' hz' hzz
    obtain ⟨p, -, rfl⟩ := hz
    obtain ⟨p', -, rfl⟩ := hz'
    simp only [hf, hG, crtMap, Function.comp_apply, ordPair, Prod.mk.injEq] at hzz ⊢
    obtain ⟨h1, h2⟩ := hzz
    have e1 := eq_of_mul_eq_mul_coprime h hm (ordType_dvd (n := m) _) (ordType_dvd (n := m) _)
      (ordType_dvd (n := n) _) (ordType_dvd (n := n) _) h1
    have e2 := eq_of_mul_eq_mul_coprime h hm (ordType_dvd (n := m) _) (ordType_dvd (n := m) _)
      (ordType_dvd (n := n) _) (ordType_dvd (n := n) _) h2
    exact ⟨⟨e1.1, e2.1⟩, ⟨e1.2, e2.2⟩⟩
  -- step 4 : the residue-splitting recoding is injective on the residues that occur
  have hdinj : Set.InjOn d (prodRes (m * n) '' (CyclicTypeChannel.box (m * n))) := by
    rintro z hz z' hz' hzz
    obtain ⟨p, -, rfl⟩ := hz
    obtain ⟨p', -, rfl⟩ := hz'
    have hlt : ∀ q : ℕ × ℕ, prodRes (m * n) q < m * n := fun q =>
      Nat.mod_lt _ (Nat.mul_pos hm hn)
    simp only [hd, Prod.mk.injEq] at hzz
    exact eq_of_mod_eq_mod h (hlt p) (hlt p') hzz.1 hzz.2
  calc IpairOrd (m * n)
      = mutInfo (CyclicTypeChannel.box (m * n)) (f ∘ (G ∘ crtMap m n)) (prodRes (m * n)) :=
        mutInfo_congr hstep1 (fun _ _ => rfl)
    _ = mutInfo (CyclicTypeChannel.box (m * n)) (G ∘ crtMap m n) (prodRes (m * n)) := by
        rw [mutInfo, mutInfo, uEnt_comp_injOn hfinj, condEnt_comp_injOn hfinj]
    _ = mutInfo (CyclicTypeChannel.box (m * n)) (G ∘ crtMap m n) (d ∘ prodRes (m * n)) := by
        rw [mutInfo, mutInfo, condEnt_cond_injOn hdinj]
    _ = mutInfo (CyclicTypeChannel.box (m * n)) (G ∘ crtMap m n) (K ∘ crtMap m n) :=
        mutInfo_congr (fun _ _ => rfl) hstep2
    _ = mutInfo ((CyclicTypeChannel.box (m * n)).image (crtMap m n)) G K :=
        (mutInfo_image_injOn (crtMap_injOn h) G K).symm
    _ = mutInfo (CyclicTypeChannel.box m ×ˢ CyclicTypeChannel.box n) G K := by rw [image_crtMap hm hn h]
    _ = IpairOrd m + IpairOrd n := by
        rw [hG, hK, mutInfo_prod hbm hbn]
        rfl
