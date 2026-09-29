-- Prove2me | Theorems.Thm_Wolf_hirsch_tfae
-- name    : Wolf.hirsch_tfae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T16:32:30.030976+00:00
-- url     : https://prove2.me/theorems/86da2e4a-b458-472d-a560-691a62853431
-- title:
--   Hirsch's theorem: a normal series with finitely generated abelian quotients, every such series, and the maximal condition
-- statement:
--   For a solvable group $\Gamma$ these three conditions are equivalent: there is a normal
--   series with every quotient finitely generated abelian; in every solvable normal series each quotient
--   is finitely generated abelian; and the subgroups of $\Gamma$ satisfy the maximal condition on
--   increasing sequences.
--
--   The chain conditions are written out elementwise, exactly as in the statement of Proposition 4.1 in
--   this mission, so that stating them needs no normality instance. Wolf cites this result and does not
--   prove it.
-- source:
--   Hirsch, K. A., On infinite soluble groups. I, Proceedings of the London Mathematical Society 44 (1938) 53–60; cited as [6] in the proof of Proposition 4.1 (p. 433) of Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658

import Mathlib

namespace Wolf

theorem hirsch_tfae {Γ : Type*} [Group Γ] [Group.IsSolvable Γ] :
    List.TFAE
      [ (∃ (u : ℕ) (B : Fin (u + 1) → Subgroup Γ), B 0 = ⊤ ∧ B (Fin.last u) = ⊥ ∧
          ∀ i : Fin u, B i.succ ≤ B i.castSucc ∧
            (∀ g ∈ B i.castSucc, ∀ x ∈ B i.succ, g * x * g⁻¹ ∈ B i.succ) ∧
            ⁅B i.castSucc, B i.castSucc⁆ ≤ B i.succ ∧
            ∃ T : Finset Γ, B i.castSucc = Subgroup.closure (T : Set Γ) ⊔ B i.succ),
        (∀ (v : ℕ) (C : Fin (v + 1) → Subgroup Γ), C 0 = ⊤ → C (Fin.last v) = ⊥ →
          (∀ i : Fin v, C i.succ ≤ C i.castSucc ∧
            (∀ g ∈ C i.castSucc, ∀ x ∈ C i.succ, g * x * g⁻¹ ∈ C i.succ) ∧
            ⁅C i.castSucc, C i.castSucc⁆ ≤ C i.succ) →
          ∀ i : Fin v, ∃ T : Finset Γ,
            C i.castSucc = Subgroup.closure (T : Set Γ) ⊔ C i.succ),
        WellFoundedGT (Subgroup Γ) ] := by
  sorry

end Wolf
