-- Prove2me | Theorems.Thm_mme_dwz_prescribed_Z_product_uniform_basis_shuffle
-- name    : mme_dwz_prescribed_Z_product_uniform_basis_shuffle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:28:59.719664+00:00
-- url     : https://prove2.me/theorems/dd34f990-7d9c-4dd6-b868-aac8f431ea15
-- title:
--   Independent uniform shuffles of actual prescribed-Z tensor products
-- statement:
--   Let $T_c$, indexed by $c\in\{1,\ldots,k\}$, be trilinear tensors over a common
--   field, with specified mode bases and Z-grade maps. Choose an integer split
--   profile $p_c$ of denominator $D_c$ and a multiplicity $m_c\geq0$ for each
--   factor, and form the actual heterogeneous product
--
--   $$
--   P=\bigotimes_{c=1}^k T_c^{\otimes D_cm_c}[p_c].
--   $$
--
--   Write $\mathcal C_c$ for the retained atomic Z-coordinate words of factor
--   $c$ and $\mathcal B_c$ for the grade words with the same exact profile. There
--   are canonical projected factor bases $B_c$, a coordinatewise grade label
--
--   $$
--   \lambda:\prod_c\mathcal C_c\longrightarrow\prod_c\mathcal B_c,
--   $$
--
--   and a uniform shuffle system on the block tuples for the independent
--   position-permutation group
--
--   $$
--   G=\prod_c\mathfrak S_{D_cm_c}.
--   $$
--
--   The factor basis inclusions are the original tensor-power word bases. The
--   product Z basis is their tensor-product basis. The grade label is surjective
--   whenever the retained product coordinate set is nonempty. The block action
--   reindexes factor $c$ by $g_c^{-1}$ and satisfies
--
--   $$
--   |\{g\in G:g\cdot b=b'\}|\,\left|\prod_c\mathcal B_c\right|=|G|.
--   $$
--
--   For every $g\in G$ there are actual mode linear equivalences $F_{g,i}$ of $P$
--   and a coordinate permutation $\pi_g$ such that
--
--   $$
--   (\bigotimes_iF_{g,i})P=P,\qquad
--   F_{g,Z}(B_w)=B_{\pi_g(w)},\qquad
--   \lambda(\pi_g(w))=g\cdot\lambda(w).
--   $$
--
--   These maps permute positions independently inside each factor and never
--   exchange differently labelled components. The theorem supplies the complete
--   tensor, basis, and uniform-block shuffle interface needed to apply exact-once
--   hole repair to a prescribed-Z standard-form product.
--
--   **Formalization Note** Empty products, zero multiplicities, and empty retained
--   spaces are included. Formal profile blocks are asserted to be attained only
--   when a retained product coordinate exists. The theorem does not identify an
--   extracted CW owner summand with this product; that normalization is a separate
--   map construction.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1, Definition 5.2, and Section 5.2, Definition 5.7 and Claims 5.8–5.10. https://arxiv.org/html/2210.10173v5#S5.SS2 . This is the derived generic heterogeneous-product tensor-and-basis interface underlying the standard-form shuffle action; it is not separately stated in this generality in the paper. Empty products and zero-length factors follow the public tensor-unit convention.

import Definitions.Def_mme_dwz_hole_cover_data
import Theorems.Thm_mme_dwz_prescribed_Z_power_uniform_basis_shuffle
import Theorems.Thm_mme_kronFin_modewise_basis_automorphisms_preserve_tensor
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Choose

open MME MME.TensorObj MME.DWZSquare MME.DWZRestrictedValue MME.DWZComponentRestriction
  Module PiTensorProduct BigOperators
open scoped Classical

universe u v w
set_option autoImplicit false

theorem mme_dwz_prescribed_Z_product_uniform_basis_shuffle {K : Type u} [Field K] (k : ℕ)
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
    ∃ system : AvailableBlockShuffle (∀ c, Block c)
      (∀ c, Equiv.Perm (Fin ((p c).length (m c)))),
      (∀ c w, (factorBasis c w : ((T c).kronPow ((p c).length (m c))).V 2) =
        kronPowModeBasis (T c) 2 (b c 2) ((p c).length (m c)) w.1) ∧
      (∀ w c, (label w c).1 = PowIndex.ofFun ((p c).length (m c))
        (fun r ↦ grade c (PowIndex.get ((p c).length (m c)) (w c).1 r))) ∧
      (Nonempty (∀ c, Coord c) → Function.Surjective label) ∧
      (∀ g w c, ((system.move g w) c).1 = PowIndex.reindex (g c).symm (w c).1) ∧
      ∀ g : ∀ c, Equiv.Perm (Fin ((p c).length (m c))),
        ∃ F : ∀ i, P.V i ≃ₗ[K] P.V i,
        ∃ perm : Equiv.Perm (∀ c, Coord c),
          PiTensorProduct.map (fun i ↦ (F i).toLinearMap) P.t = P.t ∧
          (∀ w c, (perm w c).1 = PowIndex.reindex (g c).symm (w c).1) ∧
          (∀ w, F 2 (kronFinModePiBasis k S 2 factorBasis w) =
            kronFinModePiBasis k S 2 factorBasis (perm w)) ∧
          (∀ w, label (perm w) = system.move g (label w)) := by sorry
