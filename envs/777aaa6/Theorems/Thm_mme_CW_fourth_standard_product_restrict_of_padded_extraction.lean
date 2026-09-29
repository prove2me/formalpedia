-- Prove2me | Theorems.Thm_mme_CW_fourth_standard_product_restrict_of_padded_extraction
-- name    : mme_CW_fourth_standard_product_restrict_of_padded_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T09:24:51.117521+00:00
-- url     : https://prove2.me/theorems/72d7f167-a7b1-4c2f-a283-ca57c65467e4
-- title:
--   Actual prescribed fourth-power standard products restrict from padded CW extraction
-- statement:
--   Let $K$ be any field, $N>0$, and let $CW_q$ be the canonical Coppersmith–Winograd tensor. For each full component label $c$, fix a fourth-power constituent $T_c=T_{I_cJ_cL_c}$, an integer Z-profile $p_c$ with denominator $D_c$, and a multiplicity $m_c\geq0$. Put
--
--   $$
--   n_c=D_cm_c,\qquad
--   P=\bigotimes_c T_c^{\otimes n_c}[p_c],\qquad
--   \mathcal B=\prod_c\{z_c\in\{0,\ldots,4\}^{n_c}:\#_a(z_c)=p_c(a)m_c\}.
--   $$
--
--   Each selected owner $j$ has a position bijection from $\{1,\ldots,N\}$ to the component fibers of sizes $n_c$, respecting its full component labels. Its coarse shapes are the literal constituent grades, and its Z-profile counts equal $p_c(a)m_c$. Let $Q_j$ be the actual simultaneous projection of $CW_q^{\otimes4N}$ that keeps its coarse X/Y/Z coordinates, its exact useful Z profile, and only Z coordinates compatible with no other selected owner.
--
--   Assume that the canonical retained Z-coordinate product of $P$ is nonempty and that nonhole subsets $A_j\subseteq\mathcal B$ satisfy
--
--   $$
--   |\mathcal B|\leq2^{3N},\qquad
--   \sum_j\frac{|A_j|}{|\mathcal B|}\geq3N+1.
--   $$
--
--   Assume the following precise mask correspondence: whenever an atomic Z word has owner $j$'s coarse grades and block $z\in\mathcal B$ records its left-half grades in owner $j$'s component positions, that atomic word is compatible with no other selected owner if and only if $z\in A_j$. Finally, suppose the actual padded extraction satisfies
--
--   $$
--   \bigoplus_j Q_j\preceq CW_q^{\otimes4N}.
--   $$
--
--   Then
--
--   $$
--   \boxed{P\preceq CW_q^{\otimes4N}}.
--   $$
--
--   Here $\preceq$ denotes restriction by modewise linear maps. The proof constructs the atomic grouping, coarse/profile normalization, canonical Z-basis router, literal ambient broken-copy maps, independent product shuffles, and exact-once repair. It does not assume an isomorphism or restriction from any extracted owner to a prescribed factor. The explicit mask and finite-budget hypotheses are combinatorial inputs, not tensor-realization assumptions. Full component multiplicities are not inferred from coarse marginal counts. Zero component multiplicities are included; atomic-to-block labels need not be injective.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5, particularly Lemma 5.6 and Definition 5.7 / Claims 5.8–5.10. https://arxiv.org/html/2210.10173v5#S5 . Derived finite exact-integer-profile normalization and repair theorem for canonical fourth-power constituents; the actual padded extraction and precise combinatorial mask/budget inputs remain explicit.

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

theorem mme_CW_fourth_standard_product_restrict_of_padded_extraction
    {K : Type u} [Field K] (q : ℕ) {N k R : ℕ} (hN : 0 < N)
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ)
    (component : Fin R → Fin N → Fin k) (shape : Fin k → Fin 3 → ℕ)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (hshape : ∀ c i, shape c i = (cwFourthBlockType (I c) (J c) (L c) i).val)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (positions : Fin R → Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ j c r, component j ((positions j).symm ⟨c,r⟩) = c) :
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
    ∀ copies : Fin R → MME.DWZSquare.BrokenBlockCopy Block,
      (((N * 3 + 1 : ℕ) : ℝ) ≤ ∑ j, MME.DWZSquare.nonholeFraction (copies j)) →
      (∀ j (w : WordIndex.{u} q 3 N) (z : Block),
        Graded component shape j 2 (label q 3 N w) →
        (∀ c r, PowIndex.get (n c) (z c).val r =
          fourthLeftTag (label q 3 N w ((positions j).symm ⟨c,r⟩))) →
        ((∀ j', ZCompatible component shape fourthLeftTag mu j'
            (label q 3 N w) → j' = j) ↔ z ∈ (copies j).nonholes)) →
      TensorObj.Restrict (TensorObj.bigAdd (fun j ↦ W.basisAllAllowedSubtensor B (allowed j))) W →
      TensorObj.Restrict (kronFin k S) W := by sorry
