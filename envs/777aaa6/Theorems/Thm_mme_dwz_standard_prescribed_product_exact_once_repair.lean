-- Prove2me | Theorems.Thm_mme_dwz_standard_prescribed_product_exact_once_repair
-- name    : mme_dwz_standard_prescribed_product_exact_once_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:49:32.493425+00:00
-- url     : https://prove2.me/theorems/6c216350-24f6-4371-a25c-9df9af9f93c1
-- title:
--   Exact-once hole repair for actual prescribed-Z standard products
-- statement:
--   Let $K$ be a field and let
--
--   $$
--   P=\bigotimes_{c=1}^k T_c^{\otimes D_cm_c}[p_c]
--   $$
--
--   be an actual product of prescribed-Z powers. Each factor has chosen mode
--   bases, a Z-grade map, and an integer profile $p_c$ with denominator $D_c$.
--   Let $\mathcal C_c$ be its retained atomic coordinate words and
--   $\mathcal B_c$ the grade words with the same exact counts. Put
--   $\mathcal C=\prod_c\mathcal C_c$ and $\mathcal B=\prod_c\mathcal B_c$.
--
--   There are canonical projected factor Z bases, and a label
--   $\lambda:\mathcal C\to\mathcal B$ given by applying each factor's grade map
--   coordinatewise. The basis inclusions are the original tensor-power word
--   bases, and $\lambda$ is surjective whenever $\mathcal C$ is nonempty.
--   Fix a retained coordinate witness, positive integers $N,\ell$, and nonhole
--   sets $A_1,\ldots,A_s\subseteq\mathcal B$. Suppose
--
--   $$
--   |\mathcal B|\leq 2^{N\ell},
--   \qquad
--   \sum_{j=1}^s\frac{|A_j|}{|\mathcal B|}\geq N\ell+1.
--   $$
--
--   Let $B$ be the product Z basis and let $P_j$ be the literal ambient-space
--   broken tensor obtained from $P$ by sending $B_w$ to itself when
--   $\lambda(w)\in A_j$ and to zero otherwise. Then
--
--   $$
--   P\preceq\bigoplus_{j=1}^s P_j.
--   $$
--
--   Moreover, let $Q_j$ be the actual small-space Z projection of $P$ defined
--   by any predicate $E_j$ with
--
--   $$
--   E_j(w)\iff\lambda(w)\in A_j.
--   $$
--
--   The canonical subspace inclusions give $P_j\preceq Q_j$, and hence
--
--   $$
--   P\preceq\bigoplus_{j=1}^s Q_j.
--   $$
--
--   Here $\preceq$ denotes tensor restriction by modewise linear maps. The
--   construction uses exact-once ownership after independent component shuffles;
--   no owned-block realization certificate or desired repair restriction is
--   assumed.
--
--   **Formalization Note** The bases and label are chosen before the nonhole
--   sets and budgets. Atomic coordinates need not map injectively to blocks.
--   $N$ and $\ell$ are positive parameters of the finite covering budget.
--   The theorem does not assert that an arbitrary extracted CW owner has
--   already been identified with one of the projected copies $Q_j$.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1, Definitions 5.2–5.5, and Section 5.2, Lemma 5.6 and Definition 5.7 / Claims 5.8–5.10. https://arxiv.org/html/2210.10173v5#S5.SS2 . This is a derived exact-integer-profile, basis-aware restriction formulation for actual standard products, including the explicit small-space-to-ambient projection bridge; the concrete CW owner normalization is not asserted.

import Theorems.Thm_mme_dwz_prescribed_Z_product_uniform_basis_shuffle
import Theorems.Thm_mme_dwz_generic_basis_label_hole_cover_tensor_repair
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME MME.TensorObj MME.DWZSquare MME.DWZRestrictedValue MME.DWZComponentRestriction
  Module PiTensorProduct BigOperators
open scoped Classical

universe u v
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_dwz_standard_prescribed_product_exact_once_repair {K : Type u} [Field K] (k : ℕ)
    (T : Fin k → TensorObj K 3) {I : Fin k → Fin 3 → Type u}
    (b : ∀ c i, Basis (I c i) K ((T c).V i)) (t : Fin k → ℕ)
    (grade : ∀ c, I c 2 → Fin (t c))
    (p : ∀ c, IntegerZSplitProfile (t c)) (m : Fin k → ℕ) :
    let Coord := fun c ↦ {w : PowIndex (I c 2) ((p c).length (m c)) //
      prescribedZWord (grade c) (p c) (m c) w}
    let Block := fun c ↦ {w : PowIndex (Fin (t c)) ((p c).length (m c)) //
      prescribedZWord id (p c) (m c) w}
    let S := fun c ↦ prescribedZPower (T c) (b c 2) (grade c) (p c) (m c)
    let G := fun c ↦ ((T c).kronPow ((p c).length (m c))).basisZAllowedGrading
      (kronPowModeBasis (T c) 2 (b c 2) ((p c).length (m c)))
      (prescribedZWord (grade c) (p c) (m c))
    let P := TensorObj.kronFin k S
    ∃ factorBasis : ∀ c, Basis (Coord c) K ((G c).classOf 2 0),
    ∃ label : (∀ c, Coord c) → (∀ c, Block c),
      (∀ c w, (factorBasis c w : ((T c).kronPow ((p c).length (m c))).V 2) =
        kronPowModeBasis (T c) 2 (b c 2) ((p c).length (m c)) w.1) ∧
      (∀ w c, (label w c).1 = PowIndex.ofFun ((p c).length (m c))
        (fun r ↦ grade c (PowIndex.get ((p c).length (m c)) (w c).1 r))) ∧
      (Nonempty (∀ c, Coord c) → Function.Surjective label) ∧
      ∀ (_ : Nonempty (∀ c, Coord c)) (N ell s : ℕ)
        (_ : 0 < N) (_ : 0 < ell)
        (copies : Fin s → BrokenBlockCopy (∀ c, Block c)),
        Fintype.card (∀ c, Block c) ≤ 2 ^ (N * ell) →
        ((N * ell + 1 : ℕ) : ℝ) ≤ ∑ j : Fin s, nonholeFraction (copies j) →
        let B := kronFinModePiBasis k S 2 factorBasis
        let broken : Fin s → TensorObj K 3 := fun j ↦
          { V := P.V
            t := PiTensorProduct.map
              (Function.update (fun _ ↦ LinearMap.id) 2
                (basisLabelProjection B label (copies j).nonholes)) P.t }
        TensorObj.Restrict P (TensorObj.bigAdd broken) ∧
        ∀ allowed : Fin s → (∀ c, Coord c) → Prop,
          (∀ j w, allowed j w ↔ label w ∈ (copies j).nonholes) →
          (∀ j, TensorObj.Restrict (broken j) (P.basisZAllowedSubtensor B (allowed j))) ∧
          TensorObj.Restrict P (TensorObj.bigAdd
            (fun j ↦ P.basisZAllowedSubtensor B (allowed j))) := by sorry
