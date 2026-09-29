-- Prove2me | Theorems.Thm_mme_dwz_retained_enumeration_common_z_y_isolated
-- name    : mme_dwz_retained_enumeration_common_z_y_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:57:00.948422+00:00
-- url     : https://prove2.me/theorems/58363ad7-b6be-45ac-92cb-7ad86fc3d39c
-- title:
--   Lossless retained-family enumeration preserves common Z and Y-isolation
-- statement:
--   A lossless `Fin k` enumeration of a retained asymmetric-hash family preserves the two exact structural facts needed by the DWZ Step-2 source theorem: all enumerated words have the same coarse Z word, and two enumerated copies with the same coarse Y word are the same copy. The theorem transports these facts through the literal finite-position reindexing, not through a cardinality proxy.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Steps 1 and 2, printed pp. 51--54 (PDF pp. 52--55); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_square_data

set_option autoImplicit false

theorem mme_dwz_retained_enumeration_common_z_y_isolated
    {L N k : ℕ} {Outer : Type*}
    (reindex : Fin (N + 1) ≃ Fin L)
    (K : Fin L → Fin 5)
    (I : Finset (Fin (N + 1) → Fin 15))
    (word : Outer → Fin L → Fin 15)
    (hWordInjective : Function.Injective word)
    (outer : Fin k → Outer)
    (hOuterInjective : Function.Injective outer)
    (hFixedZ : ∀ j t,
      MME.DWZSquare.shapeZ (word (outer j) t) = K t)
    (hBack : ∀ j, ∃ a ∈ I,
      word (outer j) = fun t ↦ a (reindex.symm t))
    (hYIsolatedSource : ∀ a ∈ I, ∀ b ∈ I,
      (fun t ↦ MME.DWZSquare.shapeY (a t)) =
          (fun t ↦ MME.DWZSquare.shapeY (b t)) →
        a = b) :
    (∀ j j' t,
      MME.DWZSquare.shapeZ (word (outer j) t) =
        MME.DWZSquare.shapeZ (word (outer j') t)) ∧
    ∀ j j',
      (fun t ↦ MME.DWZSquare.shapeY (word (outer j) t)) =
          (fun t ↦ MME.DWZSquare.shapeY (word (outer j') t)) →
        j = j' := by
  sorry
