-- Prove2me | Theorems.Thm_mme_complete_split_exact_product_subexponential_hole_repair
-- name    : mme_complete_split_exact_product_subexponential_hole_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:38:44.25962+00:00
-- url     : https://prove2.me/theorems/dd087cf8-1580-42af-8a9c-6c7083af6a14
-- title:
--   Subexponential repair of exact multi-term complete-profile tensors
-- statement:
--   Fix a finite ordered family of three-tensors over a field, with specified mode bases and full-word labels at level $\ell$. For every $\delta>0$ and all sufficiently large fine-position sizes $M$, there is a depth $h$ such that
--
--   $$\log(8^h)<\delta M.$$
--
--   The depth is chosen before the term lengths, exact profiles, or holes. For every length tuple $(n_t)$ with $M=2^{\max(\ell-1,0)}\sum_t n_t$ and every tuple of exact complete profiles, form the literal tensor product $S$ of the restricted powers. Use the inherited coordinate bases and literal full-label word maps, retaining their ambient power-basis identities. Write $B_i$ for the joint mode-$i$ label set across all factors.
--
--   For arbitrary deleted label sets $Q_{a,i}\subseteq B_i$ in each of $8^h$ copies, the conditions
--
--   $$8M\,|Q_{a,i}|\le |B_i|\quad\text{for every copy }a\text{ and mode }i$$
--
--   imply that $S$ restricts from the direct sum of those individually holed copies. Each copy is the actual projection onto the label complements in all three modes. Deleted label tuples may be correlated across factors.
--
--   This is the subexponential consequence of exact-interface repair. It does not assert the sharper explicit $\exp(O(M/\log M))$ copy bound, positive-tolerance assembly, a source-selection estimate, or a matrix multiplication exponent.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definition 4.1 (p.15) and Theorem 4.2 (p.18), https://arxiv.org/abs/2404.16349v2. This is its exact-profile multi-term subexponential consequence, with total fine-position size M=2^(ell−1) sum_t n_t. The finite repair mechanism follows the product-cardinality eight-box variant of Vassilevska Williams et al., arXiv:2307.07970v2, Theorem 7.2, https://arxiv.org/abs/2307.07970v2.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_modern_three_mode_projected_tensor
import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_tensor_quotient
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.ModernRepair PiTensorProduct Module
open scoped BigOperators Classical

universe u

set_option autoImplicit false

theorem mme_complete_split_exact_product_subexponential_hole_repair
    {K : Type u} [Field K] {r : ℕ}
    (T : Fin r → TensorObj K 3) {I : Fin r → Fin 3 → Type u}
    (b : ∀ t i, Basis (I t i) K ((T t).V i)) {ell : ℕ}
    (label : ∀ t i, I t i → CompleteWord ell) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ M : ℕ in atTop,
      ∃ h : ℕ, Real.log ((8 ^ h : ℕ) : ℝ) < delta * M ∧
        ∀ n : Fin r → ℕ, 2 ^ (ell - 1) * (∑ t, n t) = M →
        ∀ beta : Fin r → Fin 3 → Profile ell,
          let Coord := fun t i ↦
            {w : PowIndex (I t i) (n t) //
              ApproxConsistent (label t i) (beta t i) 0 w}
          let Block := fun t i ↦
            {w : PowIndex (CompleteWord ell) (n t) //
              ApproxConsistent id (beta t i) 0 w}
          let Term := fun t ↦ restrictedPower (T t) (b t) (label t) (beta t) 0 (n t)
          let G := fun t ↦ ((T t).kronPow (n t)).basisAllAllowedGrading
            (fun i ↦ kronPowModeBasis (T t) i (b t i) (n t))
            (fun i ↦ ApproxConsistent (label t i) (beta t i) 0)
          let S := TensorObj.kronFin r Term
          ∃ B : ∀ t i, Basis (Coord t i) K ((Term t).V i),
          ∃ blockLabel : ∀ t i, Coord t i → Block t i,
            (∀ t i w, ((G t).classOf i 0).subtype (B t i w) =
              kronPowModeBasis (T t) i (b t i) (n t) w.1) ∧
            (∀ t i w, (blockLabel t i w).1 =
              PowIndex.ofFun (n t) (fun j ↦ label t i (PowIndex.get (n t) w.1 j))) ∧
            ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (∀ t : Fin r, Block t i),
              (∀ a i, 8 * M * (holes a i).card ≤
                Fintype.card (∀ t : Fin r, Block t i)) →
              TensorObj.Restrict S
                (TensorObj.bigAdd (fun a ↦ projected S
                  (fun i ↦ kronFinModePiBasis r Term i (fun t ↦ B t i))
                  (fun i w t ↦ blockLabel t i (w t))
                  (fun i ↦ Finset.univ \ holes a i))) := by sorry
