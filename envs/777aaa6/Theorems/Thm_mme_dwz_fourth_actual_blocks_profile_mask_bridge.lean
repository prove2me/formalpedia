-- Prove2me | Theorems.Thm_mme_dwz_fourth_actual_blocks_profile_mask_bridge
-- name    : mme_dwz_fourth_actual_blocks_profile_mask_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T09:07:01.458863+00:00
-- url     : https://prove2.me/theorems/997668e0-ef63-4f22-af64-35b1f7f0ed9a
-- title:
--   Actual fourth-level CW blocks, exact profiles, and representative-independent owner masks
-- statement:
--   Fix a positive CW parameter $q$, finitely many full component labels $c$, and a chosen owner with component word $c_j:[N]\to C$. For each label, fix an integer left-Z profile $p_c$, a multiplicity $m_c$, and a total Z grade $k_c\in\{0,\ldots,8\}$. Assume an exact component-preserving position bijection
--
--   $$
--   [N]\simeq\bigsqcup_c[D_cm_c],
--   $$
--
--   that the owner's total Z grades are $k_{c_j(r)}$, and that its prescribed histogram is $p_c(a)m_c$. Require profile support only on attainable half-grades:
--
--   $$
--   p_c(a)>0\ \Longrightarrow\ a\le k_c\le a+4.
--   $$
--
--   Let $\mathcal B$ be the product of recursive grade words with these exact profiles. Let $\mathcal A$ be the global left-grade words on $[N]$ with the same componentwise histograms. Then both $\mathcal B$ and the product of retained canonical fourth-component Z-coordinate words are nonempty. There is an explicit bijection $E:\mathcal A\to\mathcal B$, with
--
--   $$
--   (Ea)_{c,r}=a_{\pi^{-1}(c,r)},\qquad
--   |\mathcal B|\le 2^{3N}.
--   $$
--
--   There is also a representative map $\rho:\mathcal B\to [q+2]^{4N}$ into actual atomic CW coordinate words. Its literal atomic grade labels satisfy the owner's coarse Z grades and exact prescribed profile, and their left-half grades are exactly $E^{-1}(z)$. Every profile-satisfying atomic word belongs to one unique block of $\mathcal B$; the atomic-word-to-block map need not be injective.
--
--   Every predicate on global blocks has exactly the same cardinality after transport along $E$. Finally, for an atomic word with the chosen owner's coarse grades and block $z$, the full Z selection predicate—coarse grade, prescribed profile, and compatibility with no different owner in the supplied family (which must be the selected family when applying the extraction theorem)—holds exactly when the representative $\rho(z)$ has that unique-owner property. Thus the nonhole mask descends to these same product block labels, independently of atomic representatives.
--
--   This supplies the finite block, availability, cardinality, and mask-identification interface between CW extraction and standard-product hole repair. It assumes neither a tensor-realization map nor a nonhole-mass estimate.
--
--   **Formalization Note** Component labels retain all distinctions supplied by the caller. Zero multiplicities and $N=0$ are allowed. The positive condition on $q$ is needed for odd atomic grades. Nonemptiness is constructed from integer profiles and canonical coordinate availability, rather than imposed as a hypothesis.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S5.SS1, Definitions 5.2–5.5 (standard tensors, available small blocks, broken copies); Section 6.1, compatibility and additional zeroing-out. This is a derived finite exact-profile, canonical-coordinate formulation of the block identification underlying those constructions.

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Theorems.Thm_mme_CW_fourth_left_grade_fiber_nonempty_iff
import Theorems.Thm_mme_dwz_fine_block_masks_depend_only_on_coarse_and_profile_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex

open MME MME.StothersFourth MME.DWZSimultaneous MME.CompleteSplit
  MME.DWZRestrictedValue MME.DWZComponentRestriction BigOperators
open scoped Classical

universe u

set_option autoImplicit false
set_option warningAsError false
set_option maxHeartbeats 400000

theorem mme_dwz_fourth_actual_blocks_profile_mask_bridge
    {C : Type*} [Fintype C] [DecidableEq C] {N R : ℕ}
    (q : ℕ) (hq : 0 < q)
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → Fin 5 → ℕ) (j : Fin R)
    (p : C → IntegerZSplitProfile 5) (m : C → ℕ) (coarse : C → Fin 9)
    (hcoarse : ∀ c, shape c 2 = (coarse c).val)
    (hmu : ∀ c a, mu 2 c a = (p c).count a * m c)
    (positions : Fin N ≃ Σ c, Fin ((p c).length (m c)))
    (hcell : ∀ c r, component j (positions.symm ⟨c, r⟩) = c)
    (hsupport : ∀ c a, 0 < (p c).count a →
      a.val ≤ (coarse c).val ∧ (coarse c).val ≤ a.val + 4) :
    let Global := {a : Fin N → Fin 5 // ∀ c z,
      Fintype.card {r : Fin N // component j r = c ∧ a r = z} =
        (p c).count z * m c}
    let Block := (c : C) → {w : PowIndex (Fin 5) ((p c).length (m c)) //
      prescribedZWord id (p c) (m c) w}
    let Coord := (c : C) → {w : PowIndex
      (ULift.{u} {x : (Fin (q+2) × Fin (q+2)) × (Fin (q+2) × Fin (q+2)) //
        cwFourthPairGrade q x = coarse c}) ((p c).length (m c)) //
      prescribedZWord (fun x ↦ cwSquarePairGrade q x.down.val.1) (p c) (m c) w}
    Nonempty Block ∧ Nonempty Coord ∧
    ∃ E : Global ≃ Block, ∃ rep : Block → WordIndex.{u} q 3 N,
      Fintype.card Block ≤ 2 ^ (N * 3) ∧
      (∀ a c r, PowIndex.get _ (E a c).val r = a.val (positions.symm ⟨c, r⟩)) ∧
      (∀ z, Graded component shape j 2 (label q 3 N (rep z)) ∧
        DWZSimultaneous.Profile component fourthLeftTag mu j 2 (label q 3 N (rep z))) ∧
      (∀ z r, fourthLeftTag (label q 3 N (rep z) r) = (E.symm z).val r) ∧
      (∀ mask : Global → Prop,
        Fintype.card {a : Global // mask a} =
          Fintype.card {z : Block // mask (E.symm z)}) ∧
      (∀ w : WordIndex.{u} q 3 N,
        DWZSimultaneous.Profile component fourthLeftTag mu j 2 (label q 3 N w) →
        ∃! z : Block, ∀ r, fourthLeftTag (label q 3 N w r) = (E.symm z).val r) ∧
      ∀ (w : WordIndex.{u} q 3 N) (z : Block),
        Graded component shape j 2 (label q 3 N w) →
        (∀ r, fourthLeftTag (label q 3 N w r) = (E.symm z).val r) →
        ((Graded component shape j 2 (label q 3 N w) ∧
          DWZSimultaneous.Profile component fourthLeftTag mu j 2 (label q 3 N w) ∧
          ∀ j', ZCompatible component shape fourthLeftTag mu j'
            (label q 3 N w) → j' = j) ↔
          ∀ j', ZCompatible component shape fourthLeftTag mu j'
            (label q 3 N (rep z)) → j' = j) := by sorry
