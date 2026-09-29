-- Prove2me | Theorems.Thm_mme_dwz_q6_022_202_component_power_exact_basis_routers
-- name    : mme_dwz_q6_022_202_component_power_exact_basis_routers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:20:31.935597+00:00
-- url     : https://prove2.me/theorems/7b0d7444-0269-4cd8-8da0-5237c58e9496
-- title:
--   Exact flat basis routers for the q=6 central component powers
-- statement:
--   For each power multiplier $m$, the canonical q=6 central component powers in rows 9 and 10 admit exact flat coordinate routers. In each orientation there is an injection from canonical coarse $Z$-basis words into the flattened matrix-multiplication coordinate set. The router preserves the full tensor and sends every canonical $Z$-basis vector to the flat coordinate vector bearing precisely that injected label.
--
--   $$
--   R_{022}(b_w)=e_{c(w)}; R_{202}(b_w)=e_{c'(w)}.
--   $$
--
--   This basis-labelled form is stronger than a bare restriction: it allows arbitrary profile predicates to be imposed later by coordinate projection, while retaining the exact two cyclic matrix-multiplication orientations.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6 and the central 022/202 component extraction used in Table 2.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_central_power_word_coordinates

open PiTensorProduct
open MME MME.DWZFineChannel MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_022_202_component_power_exact_basis_routers
    (K : Type u) [Field K] (m : ℕ) :
    (∃ (coord : PowIndex (LiftedCoarsePair.{u} 6 2)
          (MME.DWZTable2Counts.component 9 * m) ↪
            Fin ((6 ^ 2 + 2) ^ (MME.DWZTable2Counts.component 9 * m)))
        (router : ∀ s : Fin 3,
          (((canonicalComponentBlock K (9 : Fin 15)).kronPow
            (MME.DWZTable2Counts.component 9 * m)).V s) →ₗ[K]
            (MMObj K
              (1 ^ (MME.DWZTable2Counts.component 9 * m))
              (1 ^ (MME.DWZTable2Counts.component 9 * m))
              ((6 ^ 2 + 2) ^
                (MME.DWZTable2Counts.component 9 * m))).V s),
      PiTensorProduct.map router
          ((canonicalComponentBlock K (9 : Fin 15)).kronPow
            (MME.DWZTable2Counts.component 9 * m)).t =
        (MMObj K
          (1 ^ (MME.DWZTable2Counts.component 9 * m))
          (1 ^ (MME.DWZTable2Counts.component 9 * m))
          ((6 ^ 2 + 2) ^
            (MME.DWZTable2Counts.component 9 * m))).t ∧
      ∀ w, router 2 (componentPowerZBasis K (9 : Fin 15) m w) =
        central022FlatMMVec K 6
          (MME.DWZTable2Counts.component 9 * m) (coord w) 2) ∧
    (∃ (coord : PowIndex (LiftedCoarsePair.{u} 6 2)
          (MME.DWZTable2Counts.component 10 * m) ↪
            Fin ((6 ^ 2 + 2) ^ (MME.DWZTable2Counts.component 10 * m)))
        (router : ∀ s : Fin 3,
          (((canonicalComponentBlock K (10 : Fin 15)).kronPow
            (MME.DWZTable2Counts.component 10 * m)).V s) →ₗ[K]
            (MMObj K
              ((6 ^ 2 + 2) ^
                (MME.DWZTable2Counts.component 10 * m))
              (1 ^ (MME.DWZTable2Counts.component 10 * m))
              (1 ^ (MME.DWZTable2Counts.component 10 * m))).V s),
      PiTensorProduct.map router
          ((canonicalComponentBlock K (10 : Fin 15)).kronPow
            (MME.DWZTable2Counts.component 10 * m)).t =
        (MMObj K
          ((6 ^ 2 + 2) ^
            (MME.DWZTable2Counts.component 10 * m))
          (1 ^ (MME.DWZTable2Counts.component 10 * m))
          (1 ^ (MME.DWZTable2Counts.component 10 * m))).t ∧
      ∀ w, router 2 (componentPowerZBasis K (10 : Fin 15) m w) =
        central202FlatMMVec K 6
          (MME.DWZTable2Counts.component 10 * m) (coord w) 2) := by
  sorry
