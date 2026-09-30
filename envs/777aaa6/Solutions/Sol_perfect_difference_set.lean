-- Prove2me | solution 1 for perfect_difference_set
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:10:52.139779+00:00
-- url     : https://prove2.me/submissions/093580a7-4a25-4b7c-8143-dc98c4208dac

import Mathlib

/- Complete source: FieldModel.lean; SHA256: 383020495101ce944dafc371808076891ff1821088e684cff9865ccee704cd55. -/
section BundledFieldModel
section

abbrev SingerProof.field (p k : ℕ) [Fact p.Prime] := GaloisField p (3 * k)

noncomputable def SingerProof.frobenius (p k : ℕ) [Fact p.Prime] :
    field p k →+* field p k :=
  iterateFrobenius (field p k) p k

@[simp] theorem SingerProof.frobenius_apply (p k : ℕ) [Fact p.Prime] (x : field p k) :
    frobenius p k x = x ^ (p ^ k) := rfl

theorem SingerProof.frobenius_injective (p k : ℕ) [Fact p.Prime] :
    Function.Injective (frobenius p k) :=
  (frobenius p k).injective

theorem SingerProof.field_card (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    Nat.card (field p k) = (p ^ k) ^ 3 := by
  rw [GaloisField.card p (3 * k) (by omega)]
  rw [mul_comm 3 k, pow_mul]

def SingerProof.normOne (q : ℕ) (F : Type*) [Field F] : Subgroup Fˣ :=
  (powMonoidHom (q ^ 2 + q + 1) : Fˣ →* Fˣ).ker

noncomputable instance SingerProof.normOneFintype (q : ℕ) (F : Type*) [Field F] [Finite F] :
    Fintype (normOne q F) :=
  Fintype.ofFinite _

instance SingerProof.normOneIsCyclic (q : ℕ) (F : Type*) [Field F] [Finite F] :
    IsCyclic (normOne q F) := inferInstance

def SingerProof.normOneValue (q : ℕ) (F : Type*) [Field F] : normOne q F →* F :=
  (Units.coeHom F).comp (normOne q F).subtype

@[simp] theorem SingerProof.normOneValue_apply (q : ℕ) (F : Type*) [Field F]
    (a : normOne q F) : normOneValue q F a = (a.val : F) := rfl

@[simp] theorem SingerProof.normOneValue_div (q : ℕ) (F : Type*) [Field F]
    (a b : normOne q F) :
    normOneValue q F (a / b) = normOneValue q F a / normOneValue q F b :=
  Units.val_div_eq_div_val a.val b.val

theorem SingerProof.normOneValue_injective (q : ℕ) (F : Type*) [Field F] :
    Function.Injective (normOneValue q F) := by
  intro a b h
  apply Subtype.ext
  exact Units.ext h

theorem SingerProof.normOneValue_ne_zero (q : ℕ) (F : Type*) [Field F]
    (a : normOne q F) : normOneValue q F a ≠ 0 :=
  Units.ne_zero a.val

theorem SingerProof.mem_normOne_iff (q : ℕ) (F : Type*) [Field F] (a : Fˣ) :
    a ∈ normOne q F ↔ (a : F) ^ (q ^ 2 + q + 1) = 1 := by
  change a ^ (q ^ 2 + q + 1) = 1 ↔ _
  constructor
  · intro h
    exact congrArg (fun u : Fˣ => (u : F)) h
  · intro h
    apply Units.ext
    exact h

theorem SingerProof.normOneValue_pow (q : ℕ) (F : Type*) [Field F] (a : normOne q F) :
    normOneValue q F a ^ (q ^ 2 + q + 1) = 1 :=
  (mem_normOne_iff q F a.val).mp a.property

theorem SingerProof.normOne_card (q : ℕ) (F : Type*) [Field F] [Finite F]
    (hq : 1 ≤ q) (hcard : Nat.card F = q ^ 3) :
    Nat.card (normOne q F) = q ^ 2 + q + 1 := by
  rw [normOne, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hcard]
  have hq' : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hfactor : q ^ 3 = (q - 1) * (q ^ 2 + q + 1) + 1 := by
    nlinarith
  have hfactor' : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by omega
  rw [hfactor']
  exact Nat.gcd_eq_right (dvd_mul_left _ _)

theorem SingerProof.normOne_field_card (p k : ℕ) [hp : Fact p.Prime] (hk : 0 < k) :
    Nat.card (normOne (p ^ k) (field p k)) = (p ^ k) ^ 2 + p ^ k + 1 :=
  normOne_card (p ^ k) (field p k) (pow_pos hp.out.pos k) (field_card p k hk)

theorem SingerProof.norm_identity (p k : ℕ) [Fact p.Prime] (x : field p k) :
    x * frobenius p k x * frobenius p k (frobenius p k x) =
      x ^ ((p ^ k) ^ 2 + p ^ k + 1) := by
  simp only [frobenius_apply]
  rw [← pow_mul]
  calc
    x * x ^ (p ^ k) * x ^ (p ^ k * p ^ k) =
        x ^ (1 + p ^ k + p ^ k * p ^ k) := by
      rw [pow_add, pow_add, pow_one]
    _ = x ^ ((p ^ k) ^ 2 + p ^ k + 1) := by congr 1; ring

theorem SingerProof.mem_normOne_iff_norm (p k : ℕ) [Fact p.Prime] (a : (field p k)ˣ) :
    a ∈ normOne (p ^ k) (field p k) ↔
      (a : field p k) * frobenius p k (a : field p k) *
        frobenius p k (frobenius p k (a : field p k)) = 1 := by
  rw [mem_normOne_iff, norm_identity]

theorem SingerProof.normOneValue_norm (p k : ℕ) [Fact p.Prime]
    (a : normOne (p ^ k) (field p k)) :
    normOneValue (p ^ k) (field p k) a *
        frobenius p k (normOneValue (p ^ k) (field p k) a) *
        frobenius p k (frobenius p k (normOneValue (p ^ k) (field p k) a)) = 1 := by
  rw [norm_identity]
  exact normOneValue_pow _ _ a

end
end BundledFieldModel

/- Complete source: NormAlgebra.lean; SHA256: b4a4afa142ef32ff343a0dd92ec3e587d11e22a95746cb78556b7ce74ec953c3. -/
section BundledNormAlgebra
section

variable {F : Type*} [Field F]

def SingerProof.IsSingerRoot (phi : F →+* F) (x : F) : Prop :=
  phi x * x + x + 1 = 0

def SingerProof.cubicNorm (phi : F →+* F) (x : F) : F :=
  x * phi x * phi (phi x)

theorem SingerProof.singerRoot_ne_zero (phi : F →+* F) {x : F} (hx : IsSingerRoot phi x) :
    x ≠ 0 := by
  intro h
  simp [IsSingerRoot, h] at hx

theorem SingerProof.singerRoot_norm (phi : F →+* F) {x : F} (hx : IsSingerRoot phi x) :
    cubicNorm phi x = 1 := by
  change phi x * x + x + 1 = 0 at hx
  have hphi : phi (phi x) * phi x + phi x + 1 = 0 := by
    simpa only [map_add, map_mul, map_one, map_zero] using congrArg phi hx
  dsimp only [cubicNorm]
  linear_combination x * hphi - hx

theorem SingerProof.cubicNorm_ne_zero (phi : F →+* F) {x : F} (hx : cubicNorm phi x = 1) :
    x ≠ 0 := by
  intro h
  simp [cubicNorm, h] at hx

theorem SingerProof.phi_ne_one (phi : F →+* F) {x : F} (hx : x ≠ 1) : phi x ≠ 1 := by
  intro h
  apply hx
  apply phi.injective
  simpa using h

noncomputable def SingerProof.ratioFirst (phi : F →+* F) (t : F) : F :=
  (t * phi t - 1) / (1 - phi t)

theorem SingerProof.ratioFirst_relation (phi : F →+* F) {t : F} (ht : t ≠ 1) :
    ratioFirst phi t * (1 - phi t) = t * phi t - 1 := by
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr (phi_ne_one phi ht).symm)

theorem SingerProof.ratioFirst_root (phi : F →+* F) {t : F}
    (hn : cubicNorm phi t = 1) (ht : t ≠ 1) :
    IsSingerRoot phi (ratioFirst phi t) := by
  have hy := (phi_ne_one phi ht).symm
  have hz := (phi_ne_one phi (phi_ne_one phi ht)).symm
  change t * phi t * phi (phi t) = 1 at hn
  dsimp only [IsSingerRoot, ratioFirst]
  simp only [map_div₀, map_sub, map_mul, map_one]
  field_simp [sub_ne_zero.mpr hy, sub_ne_zero.mpr hz]
  linear_combination (phi t - 1) * hn

theorem SingerProof.ratioSecond_root (phi : F →+* F) {t : F}
    (hn : cubicNorm phi t = 1) (ht : t ≠ 1) :
    IsSingerRoot phi (ratioFirst phi t / t) := by
  have ht0 := cubicNorm_ne_zero phi hn
  have hy0 : phi t ≠ 0 := by
    intro h
    apply ht0
    apply phi.injective
    simpa using h
  have ha := ratioFirst_root phi hn ht
  have hr := ratioFirst_relation phi ht
  change phi (ratioFirst phi t) * ratioFirst phi t + ratioFirst phi t + 1 = 0 at ha
  change phi (ratioFirst phi t / t) * (ratioFirst phi t / t) +
    ratioFirst phi t / t + 1 = 0
  rw [map_div₀]
  field_simp [ht0, hy0]
  linear_combination ha - hr

theorem SingerProof.ratioFirst_div_second (phi : F →+* F) {t : F}
    (hn : cubicNorm phi t = 1) (ht : t ≠ 1) :
    ratioFirst phi t / (ratioFirst phi t / t) = t := by
  have ha := singerRoot_ne_zero phi (ratioFirst_root phi hn ht)
  simp [ha]

theorem SingerProof.singerRoot_ratio_unique (phi : F →+* F) {t u v : F}
    (ht : t ≠ 1) (hu : IsSingerRoot phi u) (hv : IsSingerRoot phi v)
    (hr : u / v = t) : u = ratioFirst phi t ∧ v = ratioFirst phi t / t := by
  have hu0 := singerRoot_ne_zero phi hu
  have hv0 := singerRoot_ne_zero phi hv
  have ht0 : t ≠ 0 := by rw [← hr]; exact div_ne_zero hu0 hv0
  have huv : u = t * v := (div_eq_iff hv0).mp hr
  have hphi : phi u = phi t * phi v := by rw [huv, map_mul]
  change phi u * u + u + 1 = 0 at hu
  change phi v * v + v + 1 = 0 at hv
  have hlin : u * (1 - phi t) = t * phi t - 1 := by
    rw [hphi, huv] at hu
    rw [huv]
    linear_combination hu - (t * phi t) * hv
  have hfirst : u = ratioFirst phi t :=
    (eq_div_iff (sub_ne_zero.mpr (phi_ne_one phi ht).symm)).mpr hlin
  refine ⟨hfirst, ?_⟩
  rw [← hfirst]
  apply (eq_div_iff ht0).mpr
  rw [huv]
  ring

theorem SingerProof.existsUnique_singerRoot_ratio (phi : F →+* F) {t : F}
    (hn : cubicNorm phi t = 1) (ht : t ≠ 1) :
    ∃! p : {x : F // IsSingerRoot phi x} × {x : F // IsSingerRoot phi x},
      p.1.val / p.2.val = t := by
  refine ⟨(⟨ratioFirst phi t, ratioFirst_root phi hn ht⟩,
    ⟨ratioFirst phi t / t, ratioSecond_root phi hn ht⟩),
    ratioFirst_div_second phi hn ht, ?_⟩
  intro p hp
  obtain ⟨hfirst, hsecond⟩ := singerRoot_ratio_unique phi ht p.1.property p.2.property hp
  exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond)

end
end BundledNormAlgebra

/- Complete source: Transfer.lean; SHA256: a038234c9b0ddb74f1ac1212829c8b94419f574784271608ef0886eb5c711fa6. -/
section BundledTransfer
section

theorem SingerProof.card_eq_of_unique_ratios {G : Type*} [Group G] [Fintype G]
    (q : ℕ) (hq : 2 ≤ q) (hcard : Fintype.card G = q ^ 2 + q + 1)
    (S : Finset G)
    (hS : ∀ g : G, g ≠ 1 →
      ∃! p : S × S, p.1 ≠ p.2 ∧ p.1.val / p.2.val = g) :
    S.card = q + 1 := by
  classical
  have hbij : S.offDiag.card = (Finset.univ.erase (1 : G)).card := by
    apply Finset.card_bij (fun p _ => p.1 / p.2)
    · intro p hp
      have hp' := Finset.mem_offDiag.mp hp
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact div_ne_one.mpr hp'.2.2
    · intro p hp r hr he
      obtain ⟨hp₁, hp₂, hpne⟩ := Finset.mem_offDiag.mp hp
      obtain ⟨hr₁, hr₂, hrne⟩ := Finset.mem_offDiag.mp hr
      obtain ⟨z, hz, huniq⟩ := hS (p.1 / p.2) (div_ne_one.mpr hpne)
      have hpeq : ((⟨p.1, hp₁⟩, ⟨p.2, hp₂⟩) : S × S) = z := by
        apply huniq
        exact ⟨fun h => hpne (congrArg Subtype.val h), rfl⟩
      have hreq : ((⟨r.1, hr₁⟩, ⟨r.2, hr₂⟩) : S × S) = z := by
        apply huniq
        exact ⟨fun h => hrne (congrArg Subtype.val h), he.symm⟩
      have heq := hpeq.trans hreq.symm
      exact Prod.ext (congrArg (fun a : S × S => a.1.val) heq)
        (congrArg (fun a : S × S => a.2.val) heq)
    · intro g hg
      have hg' : g ≠ 1 := (Finset.mem_erase.mp hg).1
      obtain ⟨p, hp, _⟩ := hS g hg'
      refine ⟨(p.1.val, p.2.val), ?_, hp.2⟩
      exact Finset.mem_offDiag.mpr
        ⟨p.1.property, p.2.property, fun h => hp.1 (Subtype.ext h)⟩
  have hcount : S.card * S.card - S.card = q ^ 2 + q := by
    simpa only [Finset.offDiag_card, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hcard, Nat.add_sub_cancel] using hbij
  have hm : S.card ≤ S.card * S.card := by
    by_cases hzero : S.card = 0
    · simp [hzero]
    · have hpos : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hzero
      simpa using Nat.mul_le_mul_left S.card hpos
  have heq : S.card * S.card = q ^ 2 + q + S.card := by
    have := Nat.sub_add_cancel hm
    omega
  have heqz : (S.card : ℤ) * S.card = (q : ℤ) ^ 2 + q + S.card := by
    exact_mod_cast heq
  have hfactor : ((S.card : ℤ) - (q + 1)) * ((S.card : ℤ) + q) = 0 := by
    nlinarith [heqz]
  have hqz : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hpositive : 0 < (S.card : ℤ) + q := by positivity
  have hroot : (S.card : ℤ) - (q + 1) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpositive)
  exact_mod_cast (show (S.card : ℤ) = q + 1 by omega)

theorem SingerProof.exists_zmod_difference_set {G : Type*} [CommGroup G] [Fintype G]
    [IsCyclic G] (q : ℕ) (hq : 2 ≤ q)
    (hcard : Fintype.card G = q ^ 2 + q + 1) (S : Finset G)
    (hS : ∀ g : G, g ≠ 1 →
      ∃! p : S × S, p.1 ≠ p.2 ∧ p.1.val / p.2.val = g) :
    ∃ D : Finset (ZMod (q ^ 2 + q + 1)), D.card = q + 1 ∧
      ∀ d : ZMod (q ^ 2 + q + 1), d ≠ 0 →
        ∃! p : D × D, p.1 ≠ p.2 ∧ p.1.val - p.2.val = d := by
  classical
  have hc : Nat.card G = q ^ 2 + q + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let e : Multiplicative (ZMod (q ^ 2 + q + 1)) ≃* G := by
    exact hc ▸ zmodCyclicMulEquiv (G := G) inferInstance
  let f : G ≃ ZMod (q ^ 2 + q + 1) :=
    e.symm.toEquiv.trans Multiplicative.toAdd
  have hfdiv (a b : G) : f (a / b) = f a - f b := by
    change Multiplicative.toAdd (e.symm (a / b)) =
      Multiplicative.toAdd (e.symm a) - Multiplicative.toAdd (e.symm b)
    rw [map_div]
    rfl
  have hfone : f 1 = 0 := by
    change Multiplicative.toAdd (e.symm 1) = 0
    rw [map_one]
    rfl
  let D : Finset (ZMod (q ^ 2 + q + 1)) := S.image f
  have hmem (a : S) : f a.val ∈ D :=
    Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩
  have hpre (a : D) : f.symm a.val ∈ S := by
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp a.property
    rw [← hxa, f.symm_apply_apply]
    exact hx
  refine ⟨D, ?_, ?_⟩
  · change (S.image f).card = q + 1
    rw [Finset.card_image_of_injective S f.injective]
    exact card_eq_of_unique_ratios q hq hcard S hS
  · intro d hd
    have hg : f.symm d ≠ 1 := by
      intro h
      have := congrArg f h
      rw [f.apply_symm_apply, hfone] at this
      exact hd this
    obtain ⟨p, hp, huniq⟩ := hS (f.symm d) hg
    let z : D × D := (⟨f p.1.val, hmem p.1⟩, ⟨f p.2.val, hmem p.2⟩)
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · intro h
      exact hp.1 (Subtype.ext (f.injective (congrArg Subtype.val h)))
    · change f p.1.val - f p.2.val = d
      rw [← hfdiv, hp.2, f.apply_symm_apply]
    · intro w hw
      let r : S × S :=
        (⟨f.symm w.1.val, hpre w.1⟩, ⟨f.symm w.2.val, hpre w.2⟩)
      have hr : r.1 ≠ r.2 ∧ r.1.val / r.2.val = f.symm d := by
        constructor
        · intro h
          apply hw.1
          apply Subtype.ext
          have := congrArg (fun a : S => f a.val) h
          simpa only [r, f.apply_symm_apply] using this
        · apply f.injective
          rw [hfdiv, f.apply_symm_apply]
          simpa only [r, f.apply_symm_apply] using hw.2
      have hrp := huniq r hr
      apply Prod.ext
      · apply Subtype.ext
        have := congrArg (fun a : S × S => f a.1.val) hrp
        simpa only [r, z, f.apply_symm_apply] using this
      · apply Subtype.ext
        have := congrArg (fun a : S × S => f a.2.val) hrp
        simpa only [r, z, f.apply_symm_apply] using this

end
end BundledTransfer

/- Complete source: Main.lean; SHA256: 2f8409bf1e264f22dcce80db44551ec5eb90ee6a14412fabe86b01043d6e52d7. -/
section BundledMain
section

noncomputable def SingerProof.singerSet (p k : ℕ) [Fact p.Prime] :
    Finset (normOne (p ^ k) (field p k)) := by
  classical
  exact Finset.univ.filter
    (fun g => IsSingerRoot (frobenius p k) (normOneValue (p ^ k) (field p k) g))

@[simp] theorem SingerProof.mem_singerSet (p k : ℕ) [Fact p.Prime]
    (g : normOne (p ^ k) (field p k)) :
    g ∈ singerSet p k ↔
      IsSingerRoot (frobenius p k) (normOneValue (p ^ k) (field p k) g) := by
  classical
  simp only [singerSet, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def SingerProof.rootToNormOne (p k : ℕ) [Fact p.Prime]
    (x : {x : field p k // IsSingerRoot (frobenius p k) x}) :
    normOne (p ^ k) (field p k) :=
  ⟨Units.mk0 x.val (singerRoot_ne_zero (frobenius p k) x.property),
    (mem_normOne_iff_norm p k _).mpr (singerRoot_norm (frobenius p k) x.property)⟩

@[simp] theorem SingerProof.rootToNormOne_value (p k : ℕ) [Fact p.Prime]
    (x : {x : field p k // IsSingerRoot (frobenius p k) x}) :
    normOneValue (p ^ k) (field p k) (rootToNormOne p k x) = x.val := rfl

theorem SingerProof.singerSet_unique_ratios (p k : ℕ) [Fact p.Prime]
    (g : normOne (p ^ k) (field p k)) (hg : g ≠ 1) :
    ∃! z : singerSet p k × singerSet p k,
      z.1 ≠ z.2 ∧ z.1.val / z.2.val = g := by
  classical
  let v := normOneValue (p ^ k) (field p k)
  have hvg : v g ≠ 1 := by
    intro h
    apply hg
    apply normOneValue_injective (p ^ k) (field p k)
    simpa only [map_one] using h
  have hn : cubicNorm (frobenius p k) (v g) = 1 :=
    normOneValue_norm p k g
  obtain ⟨r, hr, huniq⟩ := existsUnique_singerRoot_ratio (frobenius p k) hn hvg
  let lift : {x : field p k // IsSingerRoot (frobenius p k) x} → singerSet p k :=
    fun x => ⟨rootToNormOne p k x,
      (mem_singerSet p k _).mpr (by
        simpa only [rootToNormOne_value] using x.property)⟩
  let z : singerSet p k × singerSet p k := (lift r.1, lift r.2)
  have hzratio : z.1.val / z.2.val = g := by
    apply normOneValue_injective (p ^ k) (field p k)
    rw [normOneValue_div]
    exact hr
  have hzne : z.1 ≠ z.2 := by
    intro h
    apply hg
    rw [← hzratio, congrArg Subtype.val h, div_self']
  refine ⟨z, ⟨hzne, hzratio⟩, ?_⟩
  intro w hw
  let wr : {x : field p k // IsSingerRoot (frobenius p k) x} ×
      {x : field p k // IsSingerRoot (frobenius p k) x} :=
    (⟨v w.1.val, (mem_singerSet p k _).mp w.1.property⟩,
     ⟨v w.2.val, (mem_singerSet p k _).mp w.2.property⟩)
  have hwr : wr.1.val / wr.2.val = v g := by
    change v w.1.val / v w.2.val = v g
    rw [← normOneValue_div, hw.2]
  have heq := huniq wr hwr
  apply Prod.ext
  · apply Subtype.ext
    apply normOneValue_injective (p ^ k) (field p k)
    exact congrArg (fun s => s.1.val) heq
  · apply Subtype.ext
    apply normOneValue_injective (p ^ k) (field p k)
    exact congrArg (fun s => s.2.val) heq

end

theorem solution (q : ℕ) (hq : 2 ≤ q)
    (hpow : ∃ p k : ℕ, Nat.Prime p ∧ q = p ^ k) :
    ∃ (D : Finset (ZMod (q^2 + q + 1))),
      D.card = q + 1 ∧
      ∀ d : ZMod (q^2 + q + 1), d ≠ 0 →
        ∃! p : D × D, p.1 ≠ p.2 ∧ p.1.val - p.2.val = d := by
  obtain ⟨p, k, hp, rfl⟩ := hpow
  let : Fact p.Prime := ⟨hp⟩
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp only [hk0, pow_zero] at hq
    omega
  apply SingerProof.exists_zmod_difference_set (p ^ k) hq
    (G := SingerProof.normOne (p ^ k) (SingerProof.field p k))
    ?_ (SingerProof.singerSet p k) (SingerProof.singerSet_unique_ratios p k)
  simpa only [Nat.card_eq_fintype_card] using SingerProof.normOne_field_card p k hk
end BundledMain

