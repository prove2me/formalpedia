-- Prove2me | Theorems.Thm_mme_modern_three_mode_finite_hole_repair
-- name    : mme_modern_three_mode_finite_hole_repair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:17:04.556791+00:00
-- url     : https://prove2.me/theorems/086a0778-487a-45f4-b8e6-d709c7f3a1ce
-- title:
--   Finite three-mode hole repair with an eight-power copy budget
-- statement:
--   Let $T$ be a three-tensor over a field, with specified mode bases and finite label sets $B_i$. Suppose one finite nonempty shuffle family acts by uniform-fiber label permutations in all three modes, with actual basis-compatible modewise linear maps preserving $T$. Fix natural numbers $d,h$, and let $Q_{a,i}$ be the deleted labels in mode $i$ of copy $a\in\{1,\ldots,8^h\}$. For retained label sets $P_i$, assume
--
--   $$4d\,|Q_{a,i}|\le |B_i|\quad\text{for every }a,i,\qquad \prod_{i=1}^3|P_i|<d^h.$$
--
--   Then the tensor obtained by projecting $T$ onto the retained box $P_1\times P_2\times P_3$ restricts from the direct sum of the $8^h$ individually holed copies, where copy $a$ retains $B_i\setminus Q_{a,i}$ in mode $i$. All projections retain the original ambient tensor spaces. Empty label sets, zero-volume boxes, and $h=0$ are included. This finite theorem does not assert global hashing estimates or a bound on the matrix multiplication exponent.
-- source:
--   Product-cardinality form of the eight-box proof of Theorem7.2 in Vassilevska Williams et al., New Bounds for Matrix Multiplication: from Alpha to Omega, arXiv:2307.07970v2 (https://arxiv.org/abs/2307.07970v2), Section7. The common-shuffle ingredient is the source Lemma7.3, already formalized as mme_modern_three_mode_common_shuffle_intersection_bound. The 8^h budget simplifies finite grouping and retains the needed subexponential asymptotic order; the asymptotic estimate itself is not part of this theorem. Intended consumer: the exact complete-profile tensors in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Theorem4.2 (https://arxiv.org/abs/2404.16349v2).

import Definitions.Def_mme_modern_three_mode_projected_tensor
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_tensor_rank

open MME Module PiTensorProduct BigOperators
open MME.DWZSquare MME.ModernRepair

universe u v w

set_option autoImplicit false

theorem mme_modern_three_mode_finite_hole_repair
    {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Fin 3 → Type u} {Label : Fin 3 → Type v} {Shuffle : Type w}
    [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (label : (i : Fin 3) → ι i → Label i)
    (system : (i : Fin 3) → AvailableBlockShuffle (Label i) Shuffle)
    (maps : Shuffle → (i : Fin 3) → T.V i →ₗ[K] T.V i)
    (basisImage : Shuffle → (i : Fin 3) → ι i → ι i)
    (hbasis : ∀ g i x, maps g i (b i x) = b i (basisImage g i x))
    (hlabel : ∀ g i x,
      label i (basisImage g i x) = (system i).move g (label i x))
    (htensor : ∀ g, PiTensorProduct.map (maps g) T.t = T.t)
    (d : ℕ) :
    ∀ h : ℕ, ∀ P : (i : Fin 3) → Finset (Label i),
      ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (Label i),
      (∀ a i, 4 * d * (holes a i).card ≤ Fintype.card (Label i)) →
      (∏ i : Fin 3, (P i).card) < d ^ h →
      TensorObj.Restrict (projected T b label P)
        (TensorObj.bigAdd (fun a ↦
          projected T b label (fun i ↦ Finset.univ \ holes a i))) := by
  sorry
