-- Prove2me | Theorems.Thm_mme_dwz_table2_split_assignments_embed_typical_fiber
-- name    : mme_dwz_table2_split_assignments_embed_typical_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T14:16:53.771349+00:00
-- url     : https://prove2.me/theorems/53ee1a54-6cfa-4186-91cd-7cddfa132f7e
-- title:
--   DWZ Equation (23) assignments embed into the exact typical fiber
-- statement:
--   For a multiplier $m$, form the disjoint tagged position set used by the
--   numerator of DWZ Equation (23): one region for each boundary component and
--   one region for each interior $(+,+,k)$ class.  Give every tagged position
--   the coarse degree of its region.
--
--   The theorem proves two exact finite facts.
--
--   1. The resulting coarse word has exactly
--      $m\,\alpha_Z(k)$ positions of degree $k$, for every $k=0,\ldots,4$.
--   2. Every family of regional split words with the Table-2 cell counts maps
--      injectively to a fine word above that fixed coarse word whose global
--      fine-pair histogram is exactly $m\,\gamma$.
--
--   Thus the literal Equation-(23) numerator choices embed into the literal
--   typical fiber used as the denominator in Equation (22), without division,
--   asymptotics, or an unidentified counting object.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Definition 6.4, Claim 6.5, Lemma 6.7, conditions (a)–(c), and Equations (22)–(23), printed pp. 54–56; exact q=6 data from Section 6.3 Table 2.

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

set_option autoImplicit false

theorem mme_dwz_table2_split_assignments_embed_typical_fiber (m : ℕ) :
    let TaggedPosition :=
      Σ r : MME.DWZTable2Cardinality.SplitRegion,
        MME.DWZTable2Cardinality.RegionPosition m r
    let CoarseWord : TaggedPosition → Fin 5 := fun x ↦
      MME.DWZTable2Cardinality.coarseDegree x.1
    let TypicalFiber :=
      {small : TaggedPosition → Fin 3 × Fin 3 //
        (∀ x, MME.DWZTable2Counts.coarseOf (small x) = CoarseWord x) ∧
        ∀ p, Fintype.card {x // small x = p} =
          MME.DWZTable2Counts.gamma p * m}
    (∀ k, Fintype.card {x : TaggedPosition // CoarseWord x = k} =
      MME.DWZTable2Counts.alphaZ k * m) ∧
    ∃ encode : MME.DWZTable2Cardinality.SplitAssignments m → TypicalFiber,
      Function.Injective encode := by sorry
