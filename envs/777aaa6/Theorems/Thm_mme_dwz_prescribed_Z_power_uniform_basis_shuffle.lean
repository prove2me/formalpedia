-- Prove2me | Theorems.Thm_mme_dwz_prescribed_Z_power_uniform_basis_shuffle
-- name    : mme_dwz_prescribed_Z_power_uniform_basis_shuffle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:15:49.751235+00:00
-- url     : https://prove2.me/theorems/bea0975c-c712-41d6-b434-e161d34d1b01
-- title:
--   Exact prescribed-Z tensor shuffles with uniform fine-block action
-- statement:
--   Let $K$ be a field and $T$ a trilinear tensor over $K$, with a specified
--   basis in each mode. Give each Z-basis index a grade in a finite set of size
--   $t$. Let $p$ be an integer split profile with positive denominator $D$,
--   and let $m\geq0$. Write
--
--   $$
--   n=Dm,\qquad S=T^{\otimes n}[p].
--   $$
--
--   Here $S$ is the literal Z-only coordinate projection retaining exactly
--   $mp_a$ occurrences of grade $a$. Let $\mathcal C$ be its retained
--   atomic coordinate words and let $\mathcal B$ be the grade words with those
--   same exact counts.
--
--   There is a basis $B$ of the projected Z space indexed by $\mathcal C$,
--   whose ambient inclusion is the original tensor-power word basis. The
--   coordinatewise grade map $\lambda:\mathcal C\to\mathcal B$ is surjective
--   whenever $\mathcal C$ is nonempty.
--
--   The position-permutation group $G=\mathfrak S_n$ acts on $\mathcal B$ by
--   inverse reindexing and satisfies the exact uniformity identity
--
--   $$
--   |\{g\in G:g\cdot b=b'\}|\,|\mathcal B|=|G|
--   \qquad(b,b'\in\mathcal B).
--   $$
--
--   For every $g\in G$, there are actual mode linear equivalences $F_{g,i}$
--   of $S$ and a permutation $\pi_g$ of $\mathcal C$ such that
--
--   $$
--   (\bigotimes_i F_{g,i})S=S,\qquad
--   F_{g,Z}(B_w)=B_{\pi_g(w)},\qquad
--   \lambda(\pi_g(w))=g\cdot\lambda(w).
--   $$
--
--   The word $\pi_g(w)$ has letter $w(g^{-1}r)$ in position $r$.
--   This supplies tensor-preserving shuffles and their exact fine-block action
--   for prescribed-Z factors in a DWZ standard-form product.
--
--   **Formalization Note** The projected mode spaces are the public grading
--   classes, not new ambient spaces. The statement includes $m=0$ and empty
--   retained coordinate spaces. It does not claim that a chosen grade profile is
--   attainable without a retained coordinate witness.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.2, Definition 5.7 and Claims 5.8–5.10. https://arxiv.org/html/2210.10173v5#S5.SS2 . This derived generic single-factor theorem supplies the exact-integer-profile tensor-and-basis shuffle interface underlying those claims; it is not separately stated in this generality in the paper. The zero-length case follows the public tensor-unit convention.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_dwz_available_block_shuffle_of_pretransitive_action
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Theorems.Thm_mme_kronPow_position_permutation_recursive_basis
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate
import Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Basis.Submodule

open MME MME.TensorObj MME.DWZComponentRestriction MME.DWZRestrictedValue
  MME.DWZSquare Module PiTensorProduct
open scoped Classical

universe u
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_dwz_prescribed_Z_power_uniform_basis_shuffle {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i)) {t : ℕ}
    (grade : I 2 → Fin t) (p : IntegerZSplitProfile t) (m : ℕ) :
    let Coord := {w : PowIndex (I 2) (p.length m) // prescribedZWord grade p m w}
    let Block := {w : PowIndex (Fin t) (p.length m) // prescribedZWord id p m w}
    let S := prescribedZPower T (b 2) grade p m
    let G := (T.kronPow (p.length m)).basisZAllowedGrading
      (kronPowModeBasis T 2 (b 2) (p.length m)) (prescribedZWord grade p m)
    ∃ B : Basis Coord K (G.classOf 2 0),
    ∃ label : Coord → Block,
    ∃ system : AvailableBlockShuffle Block (Equiv.Perm (Fin (p.length m))),
      (∀ w, (B w : (T.kronPow (p.length m)).V 2) =
        kronPowModeBasis T 2 (b 2) (p.length m) w.1) ∧
      (∀ w, (label w).1 = PowIndex.ofFun (p.length m)
        (fun r ↦ grade (PowIndex.get (p.length m) w.1 r))) ∧
      (Nonempty Coord → Function.Surjective label) ∧
      (∀ e w, (system.move e w).1 = PowIndex.reindex e.symm w.1) ∧
      ∀ e : Equiv.Perm (Fin (p.length m)),
        ∃ Φ : ∀ i, G.classOf i 0 ≃ₗ[K] G.classOf i 0,
        ∃ perm : Equiv.Perm Coord,
          PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) S.t = S.t ∧
          (∀ w, (perm w).1 = PowIndex.reindex e.symm w.1) ∧
          (∀ w, Φ 2 (B w) = B (perm w)) ∧
          (∀ w, label (perm w) = system.move e (label w)) := by sorry
