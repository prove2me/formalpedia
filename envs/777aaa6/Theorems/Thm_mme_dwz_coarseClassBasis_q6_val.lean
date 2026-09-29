-- Prove2me | Theorems.Thm_mme_dwz_coarseClassBasis_q6_val
-- name    : mme_dwz_coarseClassBasis_q6_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:32:22.492911+00:00
-- url     : https://prove2.me/theorems/6e6d7b46-0432-4f7c-afdd-b2631124898d
-- title:
--   Evaluation of the canonical q=6 coarse-class basis
-- statement:
--   For the $q=6$ Coppersmith--Winograd square, fix a tensor mode and one of the five coarse grades. The canonical basis of that coarse grading class is indexed by the canonical coordinate pairs of that grade. At every such index $p$, its underlying ambient vector is exactly the original canonical square-basis vector indexed by $p$. This evaluation identity connects the abstract submodule basis used by the restricted Table-2 components to the concrete coordinate router used in the enhanced $112$ extraction.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, the canonical CW-square grading underlying Section 6.3 and the enhanced 112 component extraction, arXiv:2210.10173v5.

import Definitions.Def_mme_dwz_component_word_projection

open MME Module

universe u

set_option autoImplicit false

theorem mme_dwz_coarseClassBasis_q6_val
    (K : Type u) [Field K] (i : Fin 3) (c : Fin 5)
    (p : MME.DWZComponentRestriction.CoarsePair 6 c) :
    (MME.DWZComponentRestriction.coarseClassBasis
      (K := K) 6 i c p).1 =
      cwSquareCanonicalBasis K 6 i p.1 := by
  sorry
