-- Prove2me | solution 1 for mme_dwz_fourth_many_standard_products_restrict_of_finite_hash_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T10:26:47.4393+00:00
-- url     : https://prove2.me/submissions/97cacb40-3f38-4fc3-85ef-56d9745c631a

import Definitions.Def_mme_dwz_hole_cover_data
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Field
import Theorems.Thm_mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_dwz_common_state_CW_extraction_nonhole_index_mass
import Theorems.Thm_mme_dwz_fourth_actual_blocks_profile_mask_bridge
import Theorems.Thm_mme_CW_fourth_many_standard_products_restrict_of_padded_extraction

open MME.DWZSquare BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZMassBudget

theorem sum_enumerate {Edge : Type*} {s : ℕ} (owners : Finset Edge)
    (enumerate : Fin s ≃ ↥owners) (f : Edge → ℕ) :
    (∑ j : Fin s, f (enumerate j).val) = ∑ a ∈ owners, f a := by
  classical
  calc
    _ = ∑ a : ↥owners, f a.val := Equiv.sum_comp enumerate (fun a ↦ f a.val)
    _ = ∑ a ∈ owners, f a := Finset.sum_coe_sort owners f

/-- Convert the exact same-state counting inequality to the nonhole-fraction
budget of the Hole Lemma, without replacing block counts by coordinate counts. -/
theorem fraction_budget {Block : Type*} [Fintype Block] [Nonempty Block]
    {s : ℕ} (copies : Fin s → BrokenBlockCopy Block)
    (states targets eventCount threshold : ℕ) (hstates : 0 < states)
    (hbudget : 8 * states * threshold ≤ 3 * targets * eventCount)
    (hmass : 3 * (targets * Fintype.card Block * eventCount) ≤
      8 * (states * ∑ j : Fin s, (copies j).nonholes.card)) :
    (threshold : ℝ) ≤ ∑ j : Fin s, nonholeFraction (copies j) := by
  have hcount : threshold * Fintype.card Block ≤
      ∑ j : Fin s, (copies j).nonholes.card := by
    have hpos : 0 < 8 * states := by omega
    apply Nat.le_of_mul_le_mul_left (c := 8 * states)
    · calc
        8 * states * (threshold * Fintype.card Block) =
            (8 * states * threshold) * Fintype.card Block := by ring
        _ ≤ (3 * targets * eventCount) * Fintype.card Block :=
          Nat.mul_le_mul_right _ hbudget
        _ = 3 * (targets * Fintype.card Block * eventCount) := by ring
        _ ≤ 8 * (states * ∑ j : Fin s, (copies j).nonholes.card) := hmass
        _ = 8 * states * (∑ j : Fin s, (copies j).nonholes.card) := by ring
    · exact hpos
  have hB : (0 : ℝ) < Fintype.card Block := by
    exact_mod_cast Fintype.card_pos
  have hreal : (threshold : ℝ) * (Fintype.card Block : ℝ) ≤
      ∑ j : Fin s, ((copies j).nonholes.card : ℝ) := by
    exact_mod_cast hcount
  simp only [nonholeFraction, ← Finset.sum_div]
  exact (le_div_iff₀ hB).mpr hreal

end MME.DWZMassBudget



open MME MME.DWZSimultaneous MME.DWZRestrictedValue MME.DWZComponentRestriction
  MME.DWZSquare BigOperators
open scoped Classical
universe u
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZStandardProductMask

/-- Representatives fixed before hashing may be reused with any selected owner
family. Compatibility here quantifies over exactly that selected family. -/
theorem representative_unique_mask
    {C : Type*} [DecidableEq C] {N R : ℕ} (q : ℕ)
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → Fin 5 → ℕ)
    (p : C → IntegerZSplitProfile 5) (m : C → ℕ)
    (positions : Fin R → (Fin N ≃ Σ c, Fin ((p c).length (m c))))
    (rep : Fin R → ((c : C) → {z : PowIndex (Fin 5) ((p c).length (m c)) //
      prescribedZWord id (p c) (m c) z}) → WordIndex.{u} q 3 N)
    (hgrade : ∀ j z, Graded component shape j 2 (label q 3 N (rep j z)))
    (hlabel : ∀ j z c r,
      fourthLeftTag (label q 3 N (rep j z) ((positions j).symm ⟨c,r⟩)) =
        PowIndex.get _ (z c).val r) :
    ∀ j (w : WordIndex.{u} q 3 N) z,
      Graded component shape j 2 (label q 3 N w) →
      (∀ c r, PowIndex.get _ (z c).val r =
        fourthLeftTag (label q 3 N w ((positions j).symm ⟨c,r⟩))) →
      ((∀ j', ZCompatible component shape fourthLeftTag mu j'
          (label q 3 N w) → j' = j) ↔
        ∀ j', ZCompatible component shape fourthLeftTag mu j'
          (label q 3 N (rep j z)) → j' = j) := by
  intro j w z hw hz
  have hg : ∀ r, (∑ s, (label q 3 N w r s).val) =
      ∑ s, (label q 3 N (rep j z) r s).val :=
    fun r ↦ (hw r).trans ((hgrade j z r).symm)
  have ht (r : Fin N) : fourthLeftTag (label q 3 N w r) =
      fourthLeftTag (label q 3 N (rep j z) r) := by
    obtain ⟨⟨c,t⟩, rfl⟩ := (positions j).symm.surjective r
    exact (hz c t).symm.trans (hlabel j z c t).symm
  obtain ⟨_, _, hc, _⟩ :=
    mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
      component shape fourthLeftTag mu (label q 3 N w) (label q 3 N (rep j z)) hg ht
  simp only [hc]

end MME.DWZStandardProductMask



open MME MME.TensorObj MME.StothersFourth MME.DWZSimultaneous MME.DWZOwnerMass
  MME.DWZComponentRestriction MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.CompleteSplit MME.DWZStep1Support Module PiTensorProduct BigOperators
open scoped Classical

set_option maxHeartbeats 1200000

namespace MME.DWZManyCopyStandardProductAtomic

theorem zero_copies_restrict {K : Type u} [Field K] (P W : TensorObj K 3) :
    TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin 0 ↦ P)) W := by
  refine ⟨fun _ ↦ 0, ?_⟩
  change PiTensorProduct.map (fun i ↦ (0 : W.V i →ₗ[K] PUnit)) W.t = 0
  have hz : PiTensorProduct.map (fun i ↦ (0 : W.V i →ₗ[K] PUnit)) =
      (0 : PiTensorProduct K W.V →ₗ[K] PiTensorProduct K (fun _ : Fin 3 ↦ PUnit)) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
    exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) (0 : Fin 3) rfl
  rw [hz, LinearMap.zero_apply]

end MME.DWZManyCopyStandardProductAtomic

namespace MME.DWZManyCopyCommonStateStandardProduct

theorem fourthLeftTag_reverse (v : CompleteWord 3) :
    fourthLeftTag (reverseWord v) = Fin.rev (fourthLeftTag v) := by
  apply Fin.ext
  simp only [fourthLeftTag, reverseWord, Fin.val_rev]
  have h0 := (v 0).isLt
  have h1 := (v 1).isLt
  omega

/-- The finite fourth-level pipeline: a single hash state, its actual blocks,
its actual canonical normalization, and its repair budget. No tensor
realization, mask descent, or nonemptiness certificate is assumed. -/
theorem finite_hash_to_many_actual_standard_products
    {K : Type u} [Field K] (q N H modulus R k r : ℕ)
    [NeZero modulus] (hq : 0 < q) (hN : 0 < N)
    (I J L : Fin k → Fin 9)
    (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hsum : ∀ c, shape c 0 + shape c 1 + shape c 2 = 8)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ a, mu 2 c a = mu 1 c (Fin.rev a))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ a, mu 2 c a = mu 0 c (Fin.rev a))
    (marginal : Fin 3 → ℕ → ℕ)
    (targets ambient : Finset (Fin R)) (hsub : targets ⊆ ambient)
    (hmarginal : ∀ a ∈ targets, SameMarginal marginal (owner component shape a))
    (hcomplete : ∀ a : CoarseAddress N, Supported 8 a → SameMarginal marginal a →
      ∃ b ∈ ambient, owner component shape b = a)
    (positions : ∀ a : Fin R, a ∈ targets →
      (Fin N ≃ Σ c, Fin ((p c).length (m c))))
    (hcell : ∀ a (ha : a ∈ targets) c r, component a ((positions a ha).symm ⟨c,r⟩) = c)
    (hsupport : ∀ c a, 0 < (p c).count a →
      a.val ≤ (L c).val ∧ (L c).val ≤ a.val + 4)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (modulus / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd modulus)
    (events : Fin R → Finset ((Fin (H + 2) → ZMod modulus) × ZMod modulus))
    (hevents : ∀ a state, state ∈ events a ↔
      Retained 8 reindex S state (owner component shape a))
    (K0 pairBound degree compatibleDegree : ℕ)
    (hK : K0 = modulus * pairBound)
    (hxyBudget : 4 * degree ≤ modulus) (hzBudget : 8 * compatibleDegree ≤ modulus)
    (hsingle : ∀ a ∈ targets, (events a).card = K0)
    (hx : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 0 = owner component shape a 0)).card ≤ degree)
    (hy : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 1 = owner component shape a 1)).card ≤ degree)
    (hzCard : ∀ a ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape a 2 f ∧ Profile component fourthLeftTag mu a 2 f →
      (targets.filter (fun b ↦ b ≠ a ∧ ZCompatible component shape fourthLeftTag mu b f)).card ≤
        compatibleDegree)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient, b ≠ a →
      (owner component shape b 0 = owner component shape a 0 ∨
        owner component shape b 1 = owner component shape a 1) →
      (events a ∩ events b).card ≤ pairBound)
    (hzPair : ∀ a ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape a 2 f ∧ Profile component fourthLeftTag mu a 2 f →
      ∀ b ∈ targets, b ≠ a → ZCompatible component shape fourthLeftTag mu b f →
      (events a ∩ events b).card ≤ pairBound)
    (hbudget : 8 * Fintype.card ((Fin (H + 2) → ZMod modulus) × ZMod modulus) *
      (r * (N * 3 + 2)) ≤ 3 * targets.card * K0) :
    TensorObj.Restrict
      (bigAdd (fun _ : Fin r ↦ kronFin k (fun c ↦ prescribedZPower
        (cwFourthConstituent K q (I c) (J c) (L c))
        (constituentBasis K q (I c) (J c) (L c) 2)
        (fun a : LiftedCoarseCoordinate.{u} q (L c) ↦ cwSquarePairGrade q a.down.val.1)
        (p c) (m c))))
      ((CWObj K q).kronPow (N * 4)) := by
  classical
  by_cases hr : r = 0
  · subst r
    exact DWZManyCopyStandardProductAtomic.zero_copies_restrict _ _
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  let Block := (c : Fin k) → {w : PowIndex (Fin 5) ((p c).length (m c)) //
    prescribedZWord id (p c) (m c) w}
  have hstates : 0 < Fintype.card ((Fin (H + 2) → ZMod modulus) × ZMod modulus) :=
    Fintype.card_pos
  have htargets : targets.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hh
    have hc : targets.card = 0 := by omega
    rw [hc, Nat.mul_zero, Nat.zero_mul] at hbudget
    have hp : 0 < 8 * Fintype.card ((Fin (H + 2) → ZMod modulus) × ZMod modulus) *
        (r * (N * 3 + 2)) := by positivity
    omega
  obtain ⟨a0, ha0⟩ := htargets
  have hcoarse (c : Fin k) : shape c 2 = (L c).val := hshape c 2
  have hdata (a : ↥targets) := mme_dwz_fourth_actual_blocks_profile_mask_bridge.{u}
    q hq component shape mu a.val p m L hcoarse hmu (positions a.val a.property)
    (hcell a.val a.property) hsupport
  letI : Nonempty Block := (hdata ⟨a0, ha0⟩).1
  have hcoord := (hdata ⟨a0, ha0⟩).2.1
  choose E rep hcard hE hrep htag hmaskcard hunique hmaskdata using
    fun a : ↥targets ↦ (hdata a).2.2
  let embed (a : Fin R) (z : Block) : FineWord 3 N :=
    if ha : a ∈ targets then label q 3 N (rep ⟨a, ha⟩ z) else fun _ _ ↦ 0
  have huseful (a : Fin R) (ha : a ∈ targets) (z : Block) :
      Graded component shape a 2 (embed a z) ∧
        Profile component fourthLeftTag mu a 2 (embed a z) := by
    simp only [embed, dif_pos ha]
    exact hrep ⟨a, ha⟩ z
  have hzc (a : Fin R) (ha : a ∈ targets) (z : Block) :
      (competitors targets embed (fun f b ↦ ZCompatible component shape fourthLeftTag mu b f)
        a z).card ≤ compatibleDegree :=
    hzCard a ha (embed a z) (huseful a ha z)
  have hzp (a : Fin R) (ha : a ∈ targets) (z : Block) (b : Fin R)
      (hb : b ∈ competitors targets embed
        (fun f b ↦ ZCompatible component shape fourthLeftTag mu b f) a z) :
      (events a ∩ events b).card ≤ pairBound := by
    obtain ⟨hbt, hba, hbc⟩ := Finset.mem_filter.mp hb
    exact hzPair a ha (embed a z) (huseful a ha z) b hbt hba hbc
  obtain ⟨state, s, enumerate, hextract, hnonholes, hmass⟩ :=
    mme_dwz_common_state_CW_extraction_nonhole_index_mass
      (K := K) q 3 N H modulus R component shape hsum marginal targets ambient hsub
      hmarginal hcomplete reindex S hSrange hSfree hpodd events hevents
      fourthLeftTag Fin.rev (fun x ↦ Fin.rev_rev x) fourthLeftTag_reverse
      mu hmuX hmuY embed huseful K0 pairBound degree compatibleDegree hK
      hxyBudget hzBudget hsingle hx hy hzc hxyPair hzp
  let owners := selected targets ambient events
    (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state
  have hselected (j : Fin s) : (enumerate j).val ∈ targets :=
    (Finset.mem_filter.mp (enumerate j).property).1
  let index (j : Fin s) : ↥targets := ⟨(enumerate j).val, hselected j⟩
  let chosen : Fin s → Fin N → Fin k := fun j t ↦ component (enumerate j).val t
  let pos (j : Fin s) := positions (enumerate j).val (hselected j)
  let representatives (j : Fin s) (z : Block) := rep (index j) z
  let copies (j : Fin s) : BrokenBlockCopy Block :=
    ⟨nonholes owners embed (fun f b ↦ ZCompatible component shape fourthLeftTag mu b f)
      (enumerate j).val⟩
  have hsumcopies : (∑ j : Fin s, (copies j).nonholes.card) =
      ∑ a ∈ owners,
        (nonholes owners embed
          (fun f b ↦ ZCompatible component shape fourthLeftTag mu b f) a).card :=
    DWZMassBudget.sum_enumerate owners enumerate
      (fun a ↦ (nonholes owners embed
        (fun f b ↦ ZCompatible component shape fourthLeftTag mu b f) a).card)
  have hmass' : 3 * (targets.card * Fintype.card Block * K0) ≤
      8 * (Fintype.card ((Fin (H + 2) → ZMod modulus) × ZMod modulus) *
        ∑ j : Fin s, (copies j).nonholes.card) := by
    rw [hsumcopies]
    exact hmass
  have hfraction : ((r * (N * 3 + 2) : ℕ) : ℝ) ≤
      ∑ j : Fin s, nonholeFraction (copies j) :=
    DWZMassBudget.fraction_budget copies _ targets.card K0 (r * (N * 3 + 2))
      hstates hbudget hmass'
  have hrepgrade (j : Fin s) (z : Block) :
      Graded chosen shape j 2 (label q 3 N (representatives j z)) :=
    (hrep (index j) z).1
  have hrepprofile (j : Fin s) (z : Block) :
      Profile chosen fourthLeftTag mu j 2 (label q 3 N (representatives j z)) :=
    (hrep (index j) z).2
  have hreplabel (j : Fin s) (z : Block) (c : Fin k) (r : Fin ((p c).length (m c))) :
      fourthLeftTag (label q 3 N (representatives j z) ((pos j).symm ⟨c,r⟩)) =
        PowIndex.get _ (z c).val r := by
    have he := hE (index j) ((E (index j)).symm z) c r
    rw [Equiv.apply_symm_apply] at he
    exact (htag (index j) z ((pos j).symm ⟨c,r⟩)).trans he.symm
  have hrepresentativeMask := DWZStandardProductMask.representative_unique_mask
    q chosen shape mu p m pos representatives hrepgrade hreplabel
  have hcopy (j : Fin s) (z : Block) :
      z ∈ (copies j).nonholes ↔
        ∀ j', ZCompatible chosen shape fourthLeftTag mu j'
          (label q 3 N (representatives j z)) → j' = j := by
    have h := hnonholes j z
    have he : embed (enumerate j).val z = label q 3 N (representatives j z) := by
      simp only [embed, dif_pos (hselected j)]
      rfl
    rw [he] at h
    exact h.trans ⟨fun hh ↦ hh.2.2,
      fun hh ↦ ⟨hrepgrade j z, hrepprofile j z, hh⟩⟩
  have hfraction' : (r : ℝ) * ((N * 3 + 2 : ℕ) : ℝ) ≤
      ∑ j : Fin s, nonholeFraction (copies j) := by
    simpa only [Nat.cast_mul] using hfraction
  apply mme_CW_fourth_many_standard_products_restrict_of_padded_extraction (K := K) q r hN
    I J L p m chosen shape mu hshape hmu pos
    (fun j ↦ hcell (enumerate j).val (hselected j)) hcoord (hcard ⟨a0, ha0⟩)
    copies hfraction'
  · intro j w z hg hz
    exact (hrepresentativeMask j w z hg hz).trans (hcopy j z).symm
  · exact hextract

end MME.DWZManyCopyCommonStateStandardProduct


theorem solution
    {K : Type u} [Field K] (q N H modulus R k r : ℕ)
    [NeZero modulus] (hq : 0 < q) (hN : 0 < N)
    (I J L : Fin k → Fin 9)
    (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hsum : ∀ c, shape c 0 + shape c 1 + shape c 2 = 8)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ a, mu 2 c a = mu 1 c (Fin.rev a))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ a, mu 2 c a = mu 0 c (Fin.rev a))
    (marginal : Fin 3 → ℕ → ℕ)
    (targets ambient : Finset (Fin R)) (hsub : targets ⊆ ambient)
    (hmarginal : ∀ a ∈ targets, SameMarginal marginal (owner component shape a))
    (hcomplete : ∀ a : CoarseAddress N, Supported 8 a → SameMarginal marginal a →
      ∃ b ∈ ambient, owner component shape b = a)
    (positions : ∀ a : Fin R, a ∈ targets →
      (Fin N ≃ Σ c, Fin ((p c).length (m c))))
    (hcell : ∀ a (ha : a ∈ targets) c r, component a ((positions a ha).symm ⟨c,r⟩) = c)
    (hsupport : ∀ c a, 0 < (p c).count a →
      a.val ≤ (L c).val ∧ (L c).val ≤ a.val + 4)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (modulus / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd modulus)
    (events : Fin R → Finset ((Fin (H + 2) → ZMod modulus) × ZMod modulus))
    (hevents : ∀ a state, state ∈ events a ↔
      Retained 8 reindex S state (owner component shape a))
    (K0 pairBound degree compatibleDegree : ℕ)
    (hK : K0 = modulus * pairBound)
    (hxyBudget : 4 * degree ≤ modulus) (hzBudget : 8 * compatibleDegree ≤ modulus)
    (hsingle : ∀ a ∈ targets, (events a).card = K0)
    (hx : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 0 = owner component shape a 0)).card ≤ degree)
    (hy : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 1 = owner component shape a 1)).card ≤ degree)
    (hzCard : ∀ a ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape a 2 f ∧ Profile component fourthLeftTag mu a 2 f →
      (targets.filter (fun b ↦ b ≠ a ∧ ZCompatible component shape fourthLeftTag mu b f)).card ≤
        compatibleDegree)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient, b ≠ a →
      (owner component shape b 0 = owner component shape a 0 ∨
        owner component shape b 1 = owner component shape a 1) →
      (events a ∩ events b).card ≤ pairBound)
    (hzPair : ∀ a ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape a 2 f ∧ Profile component fourthLeftTag mu a 2 f →
      ∀ b ∈ targets, b ≠ a → ZCompatible component shape fourthLeftTag mu b f →
      (events a ∩ events b).card ≤ pairBound)
    (hbudget : 8 * Fintype.card ((Fin (H + 2) → ZMod modulus) × ZMod modulus) *
      (r * (N * 3 + 2)) ≤ 3 * targets.card * K0) :
    TensorObj.Restrict
      (bigAdd (fun _ : Fin r ↦ kronFin k (fun c ↦ prescribedZPower
        (cwFourthConstituent K q (I c) (J c) (L c))
        (constituentBasis K q (I c) (J c) (L c) 2)
        (fun a : LiftedCoarseCoordinate.{u} q (L c) ↦ cwSquarePairGrade q a.down.val.1)
        (p c) (m c))))
      ((CWObj K q).kronPow (N * 4)) := by
  exact MME.DWZManyCopyCommonStateStandardProduct.finite_hash_to_many_actual_standard_products
    q N H modulus R k r hq hN I J L p m component shape hshape hsum mu hmu hmuX hmuY
    marginal targets ambient hsub hmarginal hcomplete positions hcell hsupport
    reindex S hSrange hSfree hpodd events hevents K0 pairBound degree compatibleDegree
    hK hxyBudget hzBudget hsingle hx hy hzCard hxyPair hzPair hbudget
