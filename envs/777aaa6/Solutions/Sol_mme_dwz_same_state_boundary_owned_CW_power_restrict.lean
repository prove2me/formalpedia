-- Prove2me | solution 1 for mme_dwz_same_state_boundary_owned_CW_power_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T09:45:31.304101+00:00
-- url     : https://prove2.me/submissions/dd14df70-4525-4a3c-b91d-df43322ffdc9

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Theorems.Thm_mme_modern_grouped_fine_y_then_z_direct_sum_restrict
import Theorems.Thm_mme_modern_CW_power_nonzero_coefficient_fine_support
import Theorems.Thm_mme_modern_CW_power_nonzero_coefficient_boundary_histograms
import Theorems.Thm_mme_type2_threeAP_hash_retains_ambient_completion
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_identity
import Theorems.Thm_mme_CW_three_canonical_support
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open BigOperators
open MME Module MME.TensorObj MME.CompleteSplit MME.DWZStep1Support
universe u v w
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZSimultaneous

theorem tagged_fiber_card
    {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U] [DecidableEq W]
    (P : A → Prop) [DecidablePred P] (f : A → U) (tag : U → W) (w : W) :
    Fintype.card {a : A // P a ∧ tag (f a) = w} =
      ∑ u, if tag u = w then Fintype.card {a : A // P a ∧ f a = u} else 0 := by
  classical
  simp only [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : tag u = w
  · rw [if_pos hu]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · rintro ⟨ha, hf⟩
      exact ⟨⟨ha, by simpa only [hf] using hu⟩, hf⟩
  · rw [if_neg hu]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact hu (by simpa only [ha.2] using ha.1.2)

theorem tagged_histograms_eq
    {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U] [DecidableEq W]
    (P : A → Prop) [DecidablePred P] (f g : A → U) (tag : U → W)
    (hcount : ∀ u, Fintype.card {a : A // P a ∧ f a = u} =
      Fintype.card {a : A // P a ∧ g a = u}) (w : W) :
    Fintype.card {a : A // P a ∧ tag (f a) = w} =
      Fintype.card {a : A // P a ∧ tag (g a) = w} := by
  rw [tagged_fiber_card, tagged_fiber_card]
  simp only [hcount]

theorem reflected_tagged_histograms_eq
    {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U] [DecidableEq W]
    (P : A → Prop) [DecidablePred P] (f g : A → U)
    (rev : U → U) (hrev : Function.Involutive rev)
    (tag : U → W) (flip : W → W) (hflip : Function.Involutive flip)
    (htag : ∀ u, tag (rev u) = flip (tag u))
    (hcount : ∀ u, Fintype.card {a : A // P a ∧ f a = u} =
      Fintype.card {a : A // P a ∧ g a = rev u}) (w : W) :
    Fintype.card {a : A // P a ∧ tag (f a) = w} =
      Fintype.card {a : A // P a ∧ tag (g a) = flip w} := by
  have hcount' : ∀ u, Fintype.card {a : A // P a ∧ f a = u} =
      Fintype.card {a : A // P a ∧ rev (g a) = u} := by
    intro u
    refine (hcount u).trans (Fintype.card_congr (Equiv.subtypeEquivRight ?_))
    intro a
    apply and_congr_right
    intro _
    constructor
    · intro h
      rw [h, hrev]
    · intro h
      exact (hrev (g a)).symm.trans (congrArg rev h)
  refine (tagged_histograms_eq P f (fun a ↦ rev (g a)) tag hcount' w).trans ?_
  apply Fintype.card_congr (Equiv.subtypeEquivRight _)
  intro a
  rw [htag]
  apply and_congr_right
  intro _
  constructor
  · intro h
    exact (hflip (tag (g a))).symm.trans (congrArg flip h)
  · intro h
    rw [h, hflip]

end MME.DWZSimultaneous



namespace MME.DWZSimultaneous

theorem hash_AP_of_supported_mix {N H p : ℕ}
    (level : ℕ) (reindex : Fin (H + 1) ≃ Fin N)
    (hpodd : Odd p) (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (x y z : CoarseAddress N) (hsupport : Supported level (mix x y z)) :
    hash level reindex state 0 (x 0) + hash level reindex state 1 (y 1) =
      2 * hash level reindex state 2 (z 2) := by
  apply mme_dwz_asymmetric_hash_AP_identity hpodd
  intro t
  have ht := hsupport (reindex t)
  have ht' := congrArg (fun n : ℕ ↦ (n : ZMod p)) ht
  simpa only [fieldWord, mix, Nat.cast_add] using ht'

theorem retained_mix {N H p : ℕ}
    (level : ℕ) (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (x y z : CoarseAddress N)
    (hx : Retained level reindex S state x)
    (hy : Retained level reindex S state y)
    (hz : Retained level reindex S state z)
    (hsupport : Supported level (mix x y z)) :
    Retained level reindex S state (mix x y z) := by
  classical
  obtain ⟨a, ha, hret, _, _, _⟩ :=
    mme_type2_threeAP_hash_retains_ambient_completion p S hSrange hSfree
      (fun i a ↦ a i) (fun x y z ↦ Supported level (mix x y z))
      (hash level reindex state) (Retained level reindex S state)
      (fun _ ↦ Iff.rfl) (hash_AP_of_supported_mix level reindex hpodd state)
      ({mix x y z} : Finset (CoarseAddress N)) x y z hx hy hz hsupport
      ⟨mix x y z, Finset.mem_singleton_self _, rfl, rfl, rfl⟩
  exact (Finset.mem_singleton.mp ha) ▸ hret

theorem sameMarginal_mix {N : ℕ}
    (marginal : Fin 3 → ℕ → ℕ) (x y z : CoarseAddress N)
    (hx : SameMarginal marginal x) (hy : SameMarginal marginal y)
    (hz : SameMarginal marginal z) :
    SameMarginal marginal (mix x y z) := by
  intro i g
  fin_cases i
  · exact hx 0 g
  · exact hy 1 g
  · exact hz 2 g

theorem xy_owners_equal {N H p k : ℕ}
    (level : ℕ) (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (address : Fin k → CoarseAddress N) (hinj : Function.Injective address)
    (marginal : Fin 3 → ℕ → ℕ)
    (hmarginal : ∀ j, SameMarginal marginal (address j))
    (hretained : ∀ j, Retained level reindex S state (address j))
    (hisolated : ∀ j a, Supported level a → SameMarginal marginal a →
      Retained level reindex S state a →
      (address j 0 = a 0 ∨ address j 1 = a 1) → a = address j)
    (jx jy jz : Fin k)
    (hsupport : Supported level (mix (address jx) (address jy) (address jz))) :
    jx = jy := by
  have hret := retained_mix level reindex S hSrange hSfree hpodd state
    (address jx) (address jy) (address jz)
    (hretained jx) (hretained jy) (hretained jz) hsupport
  have hm := sameMarginal_mix marginal _ _ _
    (hmarginal jx) (hmarginal jy) (hmarginal jz)
  have hx := hisolated jx _ hsupport hm hret (Or.inl rfl)
  have hy := hisolated jy _ hsupport hm hret (Or.inr rfl)
  exact hinj (hx.symm.trans hy)

theorem reverseWord_involutive (ell : ℕ) : Function.Involutive (@reverseWord ell) := by
  intro v
  funext r
  simp only [reverseWord, Fin.rev_rev]

theorem fourthLeftTag_reverse (v : CompleteWord 3) :
    fourthLeftTag (reverseWord v) = Fin.rev (fourthLeftTag v) := by
  apply Fin.ext
  simp only [fourthLeftTag, reverseWord, Fin.val_rev]
  have h0 := (v 0).isLt
  have h1 := (v 1).isLt
  omega

theorem ZCompatible_congr_of_grade_tag
    {C : Type v} {W : Type w} [DecidableEq C] [DecidableEq W]
    {ell N k : ℕ} (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (mu : Fin 3 → C → W → ℕ)
    (f g : FineWord ell N)
    (hgrade : ∀ t, (∑ r, (f t r).val) = ∑ r, (g t r).val)
    (htag : ∀ t, tag (f t) = tag (g t)) (j : Fin k) :
    ZCompatible component shape tag mu j f ↔ ZCompatible component shape tag mu j g := by
  have hcount (c : C) (w : W) :
      Fintype.card {t : Fin N // component j t = c ∧ tag (f t) = w} =
        Fintype.card {t : Fin N // component j t = c ∧ tag (g t) = w} := by
    apply Fintype.card_congr (Equiv.subtypeEquivRight _)
    intro t
    rw [htag t]
  simp only [ZCompatible, Graded, hgrade, hcount]

theorem Allowed_congr_of_grade_tag
    {C : Type v} {W : Type w} [DecidableEq C] [DecidableEq W]
    {ell N k : ℕ} (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (mu : Fin 3 → C → W → ℕ)
    (f g : FineWord ell N)
    (hgrade : ∀ t, (∑ r, (f t r).val) = ∑ r, (g t r).val)
    (htag : ∀ t, tag (f t) = tag (g t)) (j : Fin k) (i : Fin 3) :
    Allowed component shape tag mu j i f ↔ Allowed component shape tag mu j i g := by
  have hcount (c : C) (w : W) :
      Fintype.card {t : Fin N // component j t = c ∧ tag (f t) = w} =
        Fintype.card {t : Fin N // component j t = c ∧ tag (g t) = w} := by
    apply Fintype.card_congr (Equiv.subtypeEquivRight _)
    intro t
    rw [htag t]
  simp only [Allowed, Graded, Profile, hgrade, hcount,
    ZCompatible_congr_of_grade_tag component shape tag mu f g hgrade htag]

theorem coarse_support_of_atomic_sums {ell N : ℕ}
    (word : Fin 3 → FineWord ell N)
    (hatomic : ∀ t r, (word 0 t r).val + (word 1 t r).val + (word 2 t r).val = 2) :
    Supported (2 * 2 ^ (ell - 1)) (fun i t ↦ ∑ r, (word i t r).val) := by
  intro t
  calc
    (∑ r, (word 0 t r).val) + (∑ r, (word 1 t r).val) +
        (∑ r, (word 2 t r).val) =
        ∑ r, ((word 0 t r).val + (word 1 t r).val + (word 2 t r).val) := by
          simp only [Finset.sum_add_distrib]
    _ = ∑ _r : Fin (2 ^ (ell - 1)), 2 :=
      Finset.sum_congr rfl (fun r _ ↦ hatomic t r)
    _ = 2 * 2 ^ (ell - 1) := by simp [Nat.mul_comm]

theorem source_boundary_compatibility
    {K : Type u} [Field K] {C : Type v} {W : Type w}
    [DecidableEq C] [DecidableEq W]
    (q ell N k : ℕ)
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w))
    (w : Fin 3 → WordIndex.{u} q ell N)
    (hcoeff : (Basis.piTensorProduct (basis K q ell N)).repr (source K q ell N).t w ≠ 0)
    (j : Fin k)
    (hgrades : ∀ i, Graded component shape j i (label q ell N (w i)))
    (hprofileX : ∀ c, shape c 1 = 0 → ∀ v,
      Fintype.card {t : Fin N // component j t = c ∧ tag (label q ell N (w 0) t) = v} = mu 0 c v)
    (hprofileY : ∀ c, shape c 0 = 0 → ∀ v,
      Fintype.card {t : Fin N // component j t = c ∧ tag (label q ell N (w 1) t) = v} = mu 1 c v) :
    ZCompatible component shape tag mu j (label q ell N (w 2)) := by
  have hboundary := mme_modern_CW_power_nonzero_coefficient_boundary_histograms (K := K)
    q ell N w hcoeff (component j) shape hgrades
  refine ⟨hgrades 2, ?_⟩
  intro c hc v
  rcases hc with hx | hy
  · have hfull : ∀ sigma,
        Fintype.card {t : Fin N // component j t = c ∧ label q ell N (w 2) t = sigma} =
        Fintype.card {t : Fin N // component j t = c ∧
          label q ell N (w 1) t = reverseWord sigma} := by
      intro sigma
      exact hboundary.2.1 c hx sigma
    have htagged := reflected_tagged_histograms_eq (fun t ↦ component j t = c)
      (label q ell N (w 2)) (label q ell N (w 1))
      reverseWord (reverseWord_involutive ell) tag flip hflip htag hfull v
    exact htagged.trans ((hprofileY c hx (flip v)).trans (hmuX c hx v).symm)
  · have hfull : ∀ sigma,
        Fintype.card {t : Fin N // component j t = c ∧ label q ell N (w 2) t = sigma} =
        Fintype.card {t : Fin N // component j t = c ∧
          label q ell N (w 0) t = reverseWord sigma} := by
      intro sigma
      exact hboundary.2.2 c hy sigma
    have htagged := reflected_tagged_histograms_eq (fun t ↦ component j t = c)
      (label q ell N (w 2)) (label q ell N (w 0))
      reverseWord (reverseWord_involutive ell) tag flip hflip htag hfull v
    exact htagged.trans ((hprofileX c hy (flip v)).trans (hmuY c hy v).symm)

/-- Tensor-algebra assembly. The final source-specific theorem below supplies
the coefficient-grade premise from the canonical CW support calculation.
X/Y retain only their required boundary profiles. Z retains useful tagged
blocks that are compatible with no other selected owner. Thus the projection
is on entire coarse-grade/tag blocks, not individually chosen monomials. -/
theorem simultaneous_restrict_from_coefficient_grades
    {K : Type u} [Field K] {C : Type v} {W : Type w}
    [DecidableEq C] [DecidableEq W]
    (q ell N H p k : ℕ)
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (hshape : ∀ c, shape c 0 + shape c 1 + shape c 2 = 2 * 2 ^ (ell - 1))
    (hinj : Function.Injective (owner component shape))
    (marginal : Fin 3 → ℕ → ℕ)
    (hmarginal : ∀ j, SameMarginal marginal (owner component shape j))
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (hretained : ∀ j, Retained (2 * 2 ^ (ell - 1)) reindex S state (owner component shape j))
    (hisolated : ∀ j a, Supported (2 * 2 ^ (ell - 1)) a → SameMarginal marginal a →
      Retained (2 * 2 ^ (ell - 1)) reindex S state a →
      (owner component shape j 0 = a 0 ∨ owner component shape j 1 = a 1) →
      a = owner component shape j)
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w))
    (hFine : ∀ w : Fin 3 → WordIndex.{u} q ell N,
      (Basis.piTensorProduct (basis K q ell N)).repr (source K q ell N).t w ≠ 0 →
      Supported (2 * 2 ^ (ell - 1))
        (fun i t ↦ ∑ r, (label q ell N (w i) t r).val)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦
        (source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
          (fun i w ↦ Allowed component shape tag mu j i (label q ell N w))))
      (source K q ell N) := by
  classical
  have hsupport (j : Fin k) : Supported (2 * 2 ^ (ell - 1)) (owner component shape j) :=
    fun t ↦ hshape (component j t)
  have hmixed (w : Fin 3 → WordIndex.{u} q ell N) (js : Fin 3 → Fin k)
      (hcoeff : (Basis.piTensorProduct (basis K q ell N)).repr (source K q ell N).t w ≠ 0)
      (hallowed : ∀ i, Allowed component shape tag mu (js i) i (label q ell N (w i))) :
      Supported (2 * 2 ^ (ell - 1))
        (mix (owner component shape (js 0)) (owner component shape (js 1))
          (owner component shape (js 2))) := by
    intro t
    have hs := hFine w hcoeff t
    have h0 := (hallowed 0).1 t
    have h1 := (hallowed 1).1 t
    have h2 := (hallowed 2).1 t
    change (∑ r, (label q ell N (w 0) t r).val) +
      (∑ r, (label q ell N (w 1) t r).val) +
      (∑ r, (label q ell N (w 2) t r).val) = _ at hs
    rw [h0, h1, h2] at hs
    change shape (component (js 0) t) 0 + shape (component (js 1) t) 1 +
      shape (component (js 2) t) 2 = _
    exact hs
  apply mme_modern_grouped_fine_y_then_z_direct_sum_restrict (source K q ell N)
    (basis K q ell N) (fun _ w ↦ label q ell N w)
    (Allowed component shape tag mu)
    (fun y j ↦ Graded component shape j 1 y)
    (fun z j ↦ ZCompatible component shape tag mu j z)
  · intro j j' y hallowed hcompatible
    apply hinj
    apply hisolated j (owner component shape j') (hsupport j') (hmarginal j') (hretained j')
    apply Or.inr
    funext t
    exact ((hallowed.1 t).symm.trans (hcompatible t))
  · intro w js hcoeff hallowed
    have hxy := xy_owners_equal (2 * 2 ^ (ell - 1)) reindex S hSrange hSfree hpodd
      state (owner component shape) hinj marginal hmarginal hretained hisolated
      (js 0) (js 1) (js 2) (hmixed w js hcoeff hallowed)
    simpa only [hxy] using (hallowed 1).1
  · intro j j' z hallowed hcompatible
    exact hallowed.2.2.2.2 rfl j' hcompatible
  · intro w js hcoeff hallowed hxy
    have hY : Graded component shape (js 0) 1 (label q ell N (w 1)) := by
      rw [hxy]
      exact (hallowed 1).1
    have hZ : Graded component shape (js 0) 2 (label q ell N (w 2)) := by
      intro t
      have hs := hFine w hcoeff t
      have hx := (hallowed 0).1 t
      have hy := hY t
      have ho := hshape (component (js 0) t)
      change (∑ r, (label q ell N (w 0) t r).val) +
        (∑ r, (label q ell N (w 1) t r).val) +
        (∑ r, (label q ell N (w 2) t r).val) = _ at hs
      rw [hx, hy] at hs
      change (∑ r, (label q ell N (w 2) t r).val) = _
      omega
    have hgrades : ∀ i, Graded component shape (js 0) i (label q ell N (w i)) := by
      intro i
      fin_cases i
      · exact (hallowed 0).1
      · exact hY
      · exact hZ
    have hprofileY : ∀ c, shape c 0 = 0 → ∀ v,
        Fintype.card {t : Fin N // component (js 0) t = c ∧
          tag (label q ell N (w 1) t) = v} = mu 1 c v := by
      rw [hxy]
      exact (hallowed 1).2.2.1 rfl
    exact source_boundary_compatibility (K := K) q ell N k component shape tag flip hflip htag
      mu hmuX hmuY w hcoeff (js 0) hgrades ((hallowed 0).2.1 rfl) hprofileY

end MME.DWZSimultaneous


open MME.DWZSimultaneous

theorem solution
    {K : Type u} [Field K] {C : Type v} {W : Type w}
    [DecidableEq C] [DecidableEq W]
    (q ell N H p k : ℕ)
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (hshape : ∀ c, shape c 0 + shape c 1 + shape c 2 = 2 * 2 ^ (ell - 1))
    (hinj : Function.Injective (owner component shape))
    (marginal : Fin 3 → ℕ → ℕ)
    (hmarginal : ∀ j, SameMarginal marginal (owner component shape j))
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (hretained : ∀ j, Retained (2 * 2 ^ (ell - 1)) reindex S state (owner component shape j))
    (hisolated : ∀ j a, Supported (2 * 2 ^ (ell - 1)) a → SameMarginal marginal a →
      Retained (2 * 2 ^ (ell - 1)) reindex S state a →
      (owner component shape j 0 = a 0 ∨ owner component shape j 1 = a 1) →
      a = owner component shape j)
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦
        (source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
          (fun i w ↦ Allowed component shape tag mu j i (label q ell N w))))
      (source K q ell N) := by
  apply simultaneous_restrict_from_coefficient_grades q ell N H p k component shape
    hshape hinj marginal hmarginal reindex S hSrange hSfree hpodd state hretained
    hisolated tag flip hflip htag mu hmuX hmuY
  intro w hcoeff
  apply coarse_support_of_atomic_sums (fun i ↦ label q ell N (w i))
  intro t r
  have hn := mme_modern_CW_power_nonzero_coefficient_fine_support (K := K)
    q ell N w hcoeff t r
  by_contra hbad
  exact hn (mme_CW_three_canonical_support K q
    (fun i ↦ label q ell N (w i) t r) hbad)
