-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_paired_component_source_maps
-- name    : mme_dwz_q6_common_halving_paired_component_source_maps
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:02:02.16599+00:00
-- url     : https://prove2.me/theorems/3c0a188e-d7f2-4c1c-8cdc-11b387e495c5
-- title:
--   Canonical paired source maps annihilate disallowed words after component projection
-- statement:
--   For either canonical component index $s=13$ or $s=14$, a primary family of length $N=c_s m$ with a common balanced halving admits tensor-preserving mode maps from the paired canonical powers $T_{13}^{\otimes N}\otimes T_{14}^{\otimes N}$ to the paired oriented coupled powers. If either third-mode basis word has split counts different from the prescribed profile for $(s,m)$, every retained component projection annihilates its image under these maps. The result combines basis-labelled routing with half-word mismatch vanishing; it does not assert an unconditional direct-sum extraction or factorization through the restricted source.
-- source:
--   Combines the accepted paired powered basis-labelled source router, the common-halving disallowed-word mismatch theorem, and third-mode component projection vanishing.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_kron_pow_mode_word_basis

open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
open Module TensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_paired_component_source_maps
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = MME.DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    ∃ maps : ∀ i : Fin 3,
        (TensorObj.kron
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow N)
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow N)).V i →ₗ[K]
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow N)
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).V i,
      PiTensorProduct.map maps
          (TensorObj.kron
            ((canonicalComponentBlock K (13 : Fin 15)).kronPow N)
            ((canonicalComponentBlock K (14 : Fin 15)).kronPow N)).t =
        (TensorObj.kron
          ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)).kronPow N)
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t ∧
      ∀ (w13 w14 : PowIndex (LiftedCoarsePair.{u} 6 1) N),
        ((¬ ∀ a : Fin 3,
          Fintype.card {r : Fin N // (PowIndex.get N w13 r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m) ∨
         (¬ ∀ a : Fin 3,
          Fintype.card {r : Fin N // (PowIndex.get N w14 r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m)) →
        ∀ p : Fin A × Fin H,
          ((componentProj (K := K) family halving p 2).comp (maps 2))
            (kronPowModeBasis (canonicalComponentBlock K (13 : Fin 15)) 2
                (canonicalComponentZBasis K (13 : Fin 15)) N w13 ⊗ₜ[K]
              kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
                (canonicalComponentZBasis K (14 : Fin 15)) N w14) = 0 := by sorry
