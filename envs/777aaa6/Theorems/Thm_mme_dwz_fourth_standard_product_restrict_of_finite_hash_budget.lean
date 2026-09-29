-- Prove2me | Theorems.Thm_mme_dwz_fourth_standard_product_restrict_of_finite_hash_budget
-- name    : mme_dwz_fourth_standard_product_restrict_of_finite_hash_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T09:32:53.840624+00:00
-- url     : https://prove2.me/theorems/0d081746-f316-4453-8e8f-81de3a0683ab
-- title:
--   Finite asymmetric-hash budgets realize the canonical fourth-level standard product
-- statement:
--   Let $K$ be a field, $q>0$, $N>0$, and let $C=[k]=\{0,\ldots,k-1\}$ be a finite ordered set of full component labels. For each $c\in C$, choose a supported fourth-level coarse triple $(I_c,J_c,L_c)$ with $I_c+J_c+L_c=8$, and let $T_c$ be the actual canonical constituent of the balanced fourth power of $\mathrm{CW}_q$. Choose a positive denominator $d_c$, nonnegative counts $p_c(a)$ for $0\leq a\leq4$ with $\sum_a p_c(a)=d_c$, and $m_c\geq0$. Set $n_c=d_cm_c$ and require
--   $$
--   p_c(a)>0\ \Longrightarrow\ a\leq L_c\leq a+4.
--   $$
--   The prescribed Z counts are $\mu_{Z,c}(a)=p_c(a)m_c$. On X-boundary components require $\mu_{Z,c}(a)=\mu_{Y,c}(4-a)$, and on Y-boundary components require $\mu_{Z,c}(a)=\mu_{X,c}(4-a)$.
--
--   Let $\mathcal T\subseteq\mathcal A$ be finite target and ambient families of component words $c_j:[N]\to C$. The targets have common coarse marginal counts. The ambient family represents every supported coarse address with those marginals. For each target, supply an exact component-preserving bijection
--   $$
--   [N]\simeq\bigsqcup_{c\in C}[n_c].
--   $$
--   No such common joint-type condition is required of nontarget ambient words.
--
--   Use the actual asymmetric affine hash on
--   $$
--   \Omega=(\mathbb Z/M\mathbb Z)^{H+2}\times\mathbb Z/M\mathbb Z,
--   $$
--   where $M$ is nonzero and odd, $[H+1]\simeq[N]$, and the retained hash values come from a three-term-progression-free subset of $\{0,\ldots,\lfloor M/2\rfloor-1\}$. Let $E_j\subseteq\Omega$ be exactly the retention event of address $j$.
--
--   Suppose integers $K_0,J_0,D,C_0$ satisfy
--   $$
--   K_0=MJ_0,\qquad 4D\leq M,\qquad 8C_0\leq M.
--   $$
--   Each target event has cardinality $K_0$. Each target has at most $D$ ambient addresses with the same X address, and at most $D$ with the same Y address. Distinct such target–ambient pairs have event intersection at most $J_0$.
--
--   Uniformly for every target $j$ and every fine Z-word satisfying its actual coarse grades and complete prescribed componentwise left-grade profile, at most $C_0$ other targets are Z-compatible. Here compatibility means matching coarse Z grades and the prescribed split counts on boundary components. The event intersection with each such competitor is at most $J_0$.
--
--   If the integer budget
--   $$
--   8|\Omega|(3N+1)\leq3|\mathcal T|K_0
--   $$
--   holds, then the canonical standard-form product is an actual restriction of the atomic CW power:
--   $$
--   \mathrm{CW}_q^{\otimes4N}
--   \ \longrightarrow
--   \bigotimes_{c\in C}T_c^{\otimes n_c}[p_c].
--   $$
--   Here $T_c^{\otimes n_c}[p_c]$ is the public prescribed-Z projection defined with its actual canonical constituent basis and literal left-square grades; the arrow is a mode-wise linear tensor restriction.
--
--   The theorem constructs actual available blocks, representatives fixed before selecting the hash state, the state’s owner masks, tensor normalization maps, and hole repair. It assumes none of these as tensor-realization or counting identifications. Component labels with equal coarse triples remain separate. The conclusion supplies one repaired standard product. Multiplicity-preserving repair for many disjoint copies, entropy estimates that verify the finite numerical hypotheses, positive-component value bounds, and any resulting bound on the matrix-multiplication exponent are separate.
-- source:
--   Derived finite composition of Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 (28 November 2023), https://arxiv.org/html/2210.10173v5#S5.SS1, Section 5.1 Definitions 5.2–5.5, Section 5.2 Lemma 5.6, and Sections 6.1–6.2 (asymmetric hashing, compatibility, nonhole mass, and standard-form extraction). The explicit finite 3/8 counting constants come from the proved selected-owner nonhole mass theorem used in this development. This is a derived sufficient-conditions realization theorem, not a separately numbered theorem or a numerical omega bound from the paper.

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
import Theorems.Thm_mme_CW_fourth_standard_product_restrict_of_padded_extraction

open MME MME.TensorObj MME.StothersFourth MME.DWZSimultaneous MME.DWZOwnerMass
  MME.DWZComponentRestriction MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.CompleteSplit MME.DWZStep1Support MME.DWZSquare Module PiTensorProduct BigOperators
open scoped Classical
universe u
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem mme_dwz_fourth_standard_product_restrict_of_finite_hash_budget
    {K : Type u} [Field K] (q N H modulus R k : ℕ)
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
      (N * 3 + 1) ≤ 3 * targets.card * K0) :
    TensorObj.Restrict
      (kronFin k (fun c ↦ prescribedZPower
        (cwFourthConstituent K q (I c) (J c) (L c))
        (constituentBasis K q (I c) (J c) (L c) 2)
        (fun a : LiftedCoarseCoordinate.{u} q (L c) ↦ cwSquarePairGrade q a.down.val.1)
        (p c) (m c)))
      ((CWObj K q).kronPow (N * 4)) := by sorry
