-- Prove2me | solution 1 for mme_dwz_table2_equation22_outer_layout_compatibility_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T15:18:04.205818+00:00
-- url     : https://prove2.me/submissions/c4f0aede-18d6-4731-9229-434cc29985ee

import Theorems.Thm_mme_dwz_table2_split_assignments_embed_typical_fiber
import Theorems.Thm_mme_dwz_table2_outer_layout_transport_assemble
import Theorems.Thm_mme_dwz_table2_equation22_distinct_outer_compatibility_rate

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) (hm : 0 < m)
    {Outer Position : Type*}
    [Finite Outer] [Nonempty Outer]
    [Fintype Position]
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
      (∀ I, Function.Injective (fun A ↦ assemble ⟨I, A⟩)) ∧
      ∃ small : BtypicalK,
        (Nat.card Outer : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ≤
          ((6 * ((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ)) ^ 5 *
            (∏ s : Fin 15,
              if MME.DWZSquare.shapeX s = 0 ∨
                  MME.DWZSquare.shapeY s = 0 then
                (6 *
                  ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3
              else 1) *
            (∏ k : Fin 5,
              (6 *
                ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3)) *
            (Nat.card
              {I : Outer //
                ∃ A : MME.DWZTable2Cardinality.SplitAssignments m,
                  assemble ⟨I, A⟩ = small} : ℝ) := by
  classical
  dsimp only
  let TaggedPosition :=
    Σ r : MME.DWZTable2Cardinality.SplitRegion,
      MME.DWZTable2Cardinality.RegionPosition m r
  let CoarseWord : TaggedPosition → Fin 5 := fun x ↦
    MME.DWZTable2Cardinality.coarseDegree x.1
  obtain ⟨hcanonical, _encode, _hencode⟩ :=
    mme_dwz_table2_split_assignments_embed_typical_fiber m
  let I₀ : Outer := Classical.choice (inferInstance : Nonempty Outer)
  have hK : ∀ k,
      Fintype.card {t : Position // K t = k} =
        MME.DWZTable2Counts.alphaZ k * m := by
    intro k
    let fiberEquiv :
        {x : TaggedPosition // CoarseWord x = k} ≃
          {t : Position // K t = k} :=
      Equiv.subtypeEquiv (layout I₀) (fun x ↦ by
        dsimp only [CoarseWord]
        rw [hlayout I₀ x])
    rw [← Fintype.card_congr fiberEquiv]
    exact hcanonical k
  obtain ⟨assemble, hinjective⟩ :=
    mme_dwz_table2_outer_layout_transport_assemble m K layout hlayout
  refine ⟨assemble, hinjective, ?_⟩
  exact mme_dwz_table2_equation22_distinct_outer_compatibility_rate
    m hm K hK assemble hinjective
