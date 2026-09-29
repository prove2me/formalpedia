-- Prove2me | Theorems.Thm_mme_dwz_global_exact_profile_conditioned_aggregate_selection
-- name    : mme_dwz_global_exact_profile_conditioned_aggregate_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T08:05:51.718903+00:00
-- url     : https://prove2.me/theorems/02c98e1d-4d02-4cde-9853-c471e5105979
-- title:
--   One canonical affine state preserves aggregate exact-profile nonhole mass
-- statement:
--   Fix a positive Table-2 scale, one odd common prime, a lower-half progression-free set S, an ambient marginal family A, and its exact-profile subfamily T. Suppose every selected owner has uniformly bounded X- and Y-collision degrees, every compatible fine-candidate fiber obeys the common-prime budget, and every useful-block type has the same positive cardinality cap. Then there is one canonical affine state q and an X/Y-isolated exact-profile subfamily I inside its bucket such that
--
--   $$\frac{|T|\,|S|}{2p^2}\leq\sum_{a\in I}\frac{\operatorname{mass}(q,a)}{\mathrm{cap}}.$$
--
--   Here mass(q,a) is the nonhole cardinality of the ambient conditioned broken copy for owner a at the common state q. The conclusion preserves aggregate mass and does not require every owner to be individually seven-eighths good.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.1 and Claim 6.8.

import Theorems.Thm_mme_dwz_table2_canonical_affine_selection_of_owner_mass
import Theorems.Thm_mme_dwz_global_exact_profile_owner_canonical_bucket_mass
import Definitions.Def_mme_dwz_global_ambient_conditioned_broken_copy

open MME BigOperators

set_option autoImplicit false

theorem mme_dwz_global_exact_profile_conditioned_aggregate_selection
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp4 : 4 < p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset
      (Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) → Fin 15))
    (d cap : ℕ) (hcap : 0 < cap) (hmod : 8 * d ≤ p) :
    let L := MME.DWZTable2Counts.scale * m
    let n := L - 1
    let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
      dsimp only [n, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let ExactProfile : (Fin (n + 1) → Fin 15) → Prop := fun a ↦
      ∀ s, Fintype.card {t : Fin (n + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin (n + 1) → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let ExactProfileNative : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let Tnative : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfileNative
    let native : (Fin (n + 1) → Fin 15) → Fin L → Fin 15 :=
      fun a t ↦ a (reindex.symm t)
    let grade : ∀ a,
        MME.DWZTable2StandardForm.UsefulBlock m (native a) →
          Fin L → Fin (3 * 3) := fun _ z t ↦
      MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
    let candidates : ∀ a,
        MME.DWZTable2StandardForm.UsefulBlock m (native a) →
          Finset (Fin L → Fin 15) := fun a z ↦ by
      classical
      exact Tnative.filter (fun w : Fin L → Fin 15 ↦
        (∀ t, MME.DWZSquare.shapeZ (w t) =
          MME.DWZSquare.shapeZ (native a t)) ∧
        MME.DWZStep2Source.retainedFineCompatible m
          (fun w : Fin L → Fin 15 ↦ w) (grade a z) w)
    (T ⊆ A) →
    (∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ MME.DWZSquare.shapeX (b t)) =
          (fun t ↦ MME.DWZSquare.shapeX (a t)))).card ≤ d) →
    (∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ MME.DWZSquare.shapeY (b t)) =
          (fun t ↦ MME.DWZSquare.shapeY (a t)))).card ≤ d) →
    (∀ a, a ∈ T → ∀ z, 8 * (candidates a z).card ≤ p) →
    (∀ a, a ∈ T →
      Fintype.card
          (MME.DWZTable2StandardForm.UsefulBlock m (native a)) = cap) →
    ∃ q : (Fin (n + 2) → ZMod p) × ZMod p,
      ∃ I : Finset (Fin (n + 1) → Fin 15),
        I ⊆ T ∧
        I ⊆ MME.dwzTable2AffineHashBucket S A q ∧
        (∀ e ∈ I, ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
          (fun t ↦ MME.DWZSquare.shapeX (e t)) =
              (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
            (fun t ↦ MME.DWZSquare.shapeY (e t)) =
              (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
        let mass : ((Fin (n + 2) → ZMod p) × ZMod p) →
            (Fin (n + 1) → Fin 15) → ℕ := fun q a ↦ by
          classical
          by_cases ha : a ∈ T
          · have hnative : native a ∈ Tnative := by
              simp only [Tnative, Finset.mem_filter, Finset.mem_univ,
                true_and, ExactProfileNative]
              intro s
              let E : {t : Fin L // native a t = s} ≃
                  {t : Fin (n + 1) // a t = s} :=
                reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl)
              calc
                Fintype.card {t : Fin L // native a t = s} =
                    Fintype.card {t : Fin (n + 1) // a t = s} :=
                  Fintype.card_congr E
                _ = MME.DWZTable2Counts.component s * m :=
                  (Finset.mem_filter.mp ha).2 s
            exact (MME.DWZGlobalCorrelated.ambientConditionedBrokenCopy
              m reindex Tnative (native a) hnative
                (fun t ↦ q.1 t.castSucc)).nonholes.card
          · exact 0
        ((T.card : ℝ) * (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ a ∈ I, (mass q a : ℝ) / (cap : ℝ) := by
  sorry
