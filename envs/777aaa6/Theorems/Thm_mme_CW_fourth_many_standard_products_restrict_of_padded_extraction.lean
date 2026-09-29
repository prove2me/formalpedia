-- Prove2me | Theorems.Thm_mme_CW_fourth_many_standard_products_restrict_of_padded_extraction
-- name    : mme_CW_fourth_many_standard_products_restrict_of_padded_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T10:10:48.317957+00:00
-- url     : https://prove2.me/theorems/ac187943-5428-459c-8c96-2eb144849263
-- title:
--   Many canonical fourth-power standard products from actual padded CW extraction
-- statement:
--   Let $N>0$ and $r\geq0$ be integers. Fix canonical fourth-power CW constituents $T_c=T_{I_cJ_cL_c}$, integer Z-profiles $p_c$ with denominators $D_c$, and integers $m_c\geq0$. Set
--
--   $$
--   n_c=D_cm_c,\qquad P=\bigotimes_c T_c^{\otimes n_c}[p_c],\qquad
--   \mathcal B=\prod_c\{z_c\in\{0,\ldots,4\}^{n_c}:\#_a(z_c)=p_c(a)m_c\}.
--   $$
--
--   Suppose each selected owner has a component-respecting position bijection with these exact full-label multiplicities. Its coarse shapes equal the literal constituent grades, and its useful Z-profile counts equal $p_c(a)m_c$. Write $Q_j$ for its actual projection of $CW_q^{\otimes4N}$ retaining coarse coordinates, the useful Z profile, and Z coordinates compatible with no other owner in the entire selected family.
--
--   Suppose the retained canonical Z-coordinate product is nonempty. Let $A_j\subseteq\mathcal B$ correspond exactly to these unique-owner Z coordinates via the left-half grade words in the owner's component positions. Assume
--
--   $$
--   |\mathcal B|\leq2^{3N},\qquad
--   \sum_j\frac{|A_j|}{|\mathcal B|}\geq r(3N+2),\qquad
--   \bigoplus_jQ_j\preceq CW_q^{\otimes4N}.
--   $$
--
--   Then
--
--   $$
--   \boxed{P^{\oplus r}\preceq CW_q^{\otimes4N}}.
--   $$
--
--   Here restriction is by modewise linear maps over any field. The theorem retains the multiplicity of complete standard products supplied by the nonhole budget. Owner masks always refer to the original selected family, including when broken copies are grouped for repair. The case $r=0$ and zero component multiplicities are included. No owner-to-standard-product tensor realization is assumed.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.2, Corollary 5.11, using Lemma 5.6, and Section 6.2 (Bounding the value). https://arxiv.org/html/2210.10173v5#S5.SS2 . Derived finite canonical fourth-power realization with an explicit integer requested-copy count and unchanged full-selected-family masks.

import Theorems.Thm_mme_dwz_generic_basis_label_multiple_copy_repair
import Theorems.Thm_mme_CW_atomic_fourth_component_grouping_projection_transport
import Theorems.Thm_mme_CW_fourth_component_profile_projection_normalization
import Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
import Theorems.Thm_mme_dwz_prescribed_Z_product_uniform_basis_shuffle
import Theorems.Thm_mme_dwz_generic_basis_label_hole_cover_tensor_repair
import Theorems.Thm_mme_bigAdd_mono_restrict
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj MME.StothersFourth MME.DWZStep1Support MME.DWZSimultaneous
  MME.DWZComponentRestriction MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.DWZSquare Module PiTensorProduct BigOperators
open scoped Classical
universe u v w z
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_fourth_many_standard_products_restrict_of_padded_extraction
    {K : Type u} [Field K] (q r : ℕ) {N k R : ℕ} (hN : 0 < N)
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (positions : Fin R → Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ j c t, component j ((positions j).symm ⟨c,t⟩) = c) :
    let n := fun c ↦ (p c).length (m c)
    let W := (CWObj K q).kronPow (N * 4)
    let C := fun c ↦ cwFourthConstituent K q (I c) (J c) (L c)
    let b := fun c ↦ constituentBasis K q (I c) (J c) (L c)
    let grade := fun c (a : LiftedCoarseCoordinate.{u} q (L c)) ↦
      cwSquarePairGrade q a.down.val.1
    let S := fun c ↦ prescribedZPower (C c) (b c 2) (grade c) (p c) (m c)
    let Coord := fun c ↦ {w : PowIndex (LiftedCoarseCoordinate.{u} q (L c)) (n c) //
      prescribedZWord (grade c) (p c) (m c) w}
    let Block := (c : Fin k) → {w : PowIndex (Fin 5) (n c) //
      prescribedZWord id (p c) (m c) w}
    let B := fun i ↦ kronPowModeWordBasis (CWObj K q) i
      ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (N * 4)
    let allowed := fun j i w ↦
      Graded component shape j i (label q 3 N w) ∧
      (i = 2 → Profile component fourthLeftTag mu j 2 (label q 3 N w)) ∧
      (i = 2 → ∀ j', ZCompatible component shape fourthLeftTag mu j'
        (label q 3 N w) → j' = j)
    Nonempty (∀ c, Coord c) →
    Fintype.card Block ≤ 2 ^ (N * 3) →
    ∀ copies : Fin R → BrokenBlockCopy Block,
      ((r : ℝ) * ((N * 3 + 2 : ℕ) : ℝ) ≤ ∑ j, nonholeFraction (copies j)) →
      (∀ j (w : WordIndex.{u} q 3 N) (z : Block),
        Graded component shape j 2 (label q 3 N w) →
        (∀ c t, PowIndex.get (n c) (z c).val t =
          fourthLeftTag (label q 3 N w ((positions j).symm ⟨c,t⟩))) →
        ((∀ j', ZCompatible component shape fourthLeftTag mu j'
            (label q 3 N w) → j' = j) ↔ z ∈ (copies j).nonholes)) →
      TensorObj.Restrict (TensorObj.bigAdd (fun j ↦ W.basisAllAllowedSubtensor B (allowed j))) W →
      TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin r ↦ kronFin k S)) W := by sorry
