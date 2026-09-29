-- Prove2me | Theorems.Thm_mme_dwz_table2_outer_layout_transport_assemble
-- name    : mme_dwz_table2_outer_layout_transport_assemble
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T14:30:52.81529+00:00
-- url     : https://prove2.me/theorems/6572e8eb-0da4-4625-b6f5-694a0cb6d433
-- title:
--   Coarse-preserving regional layouts yield the DWZ typical-word assembly
-- statement:
--   For every multiplier `m`, let the canonical tagged position set be the
--   disjoint union of all Table-2 boundary regions from condition (a) and the five
--   interior `(+,+,k)` regions from condition (c).  Fix a finite literal position
--   set and a coarse word `K` on it.  Suppose that every outer object supplies a
--   bijection from the canonical tagged positions to the literal positions, and
--   that this bijection preserves the coarse Z-degree at every position.
--
--   Then all independent Equation-(23) regional split assignments can be assembled
--   into literal fine-pair words over the position set.  Every assembled word
--   coarsens pointwise to `K` and has exactly `gamma(p) * m` occurrences of every
--   fine pair `p`.  For each fixed outer object, distinct regional assignments
--   assemble to distinct fine words.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Lemma 6.7 conditions (a)–(c) and Equations (22)–(23), printed pp. 55–56.

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

set_option autoImplicit false

theorem mme_dwz_table2_outer_layout_transport_assemble
    (m : ℕ)
    {Outer Position : Type*}
    [Finite Outer] [Fintype Position]
    (K : Position → Fin 5)
    (layout : ∀ _I : Outer,
      (Σ r : MME.DWZTable2Cardinality.SplitRegion,
        MME.DWZTable2Cardinality.RegionPosition m r) ≃ Position)
    (hlayout : ∀ (I : Outer) x,
      K (layout I x) = MME.DWZTable2Cardinality.coarseDegree x.1) :
    let BtypicalK :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    ∃ assemble :
        (Σ _I : Outer, MME.DWZTable2Cardinality.SplitAssignments m) →
          BtypicalK,
      ∀ I, Function.Injective (fun A ↦ assemble ⟨I, A⟩) := by sorry
