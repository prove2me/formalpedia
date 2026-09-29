-- Prove2me | Theorems.Thm_Wolf_isPolycyclic_tfae
-- name    : Wolf.isPolycyclic_tfae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T16:32:16.532777+00:00
-- url     : https://prove2.me/theorems/21aea989-1251-4370-b1b7-45e190ae421f
-- title:
--   Proposition 4.1: seven equivalent characterisations of a polycyclic group
-- statement:
--   For a solvable group $\Gamma$ the following are equivalent: (1) there is a normal series
--   with every quotient cyclic; (2) there is a normal series with every quotient finitely generated
--   abelian; (3) in every solvable normal series each quotient is finitely generated abelian; (4) each
--   quotient of the derived series is finitely generated abelian; (5) every derived subgroup is finitely
--   generated; (6) every subgroup is finitely generated; (7) the subgroups satisfy the maximal condition
--   on increasing sequences.
--
--   Condition (1) is the published definition of a polycyclic group. In conditions (2), (3) and (4) the
--   conditions on a chain are written out elementwise, so that stating them needs no normality
--   instance: each term being normal in the preceding one, each quotient being abelian, and each
--   quotient being finitely generated are each spelled out in terms of the elements of the two
--   subgroups. Condition (7) is the ascending chain condition on subgroups. Conditions (8) to (11) of
--   Wolf's proposition are a finite-index subgroup that is finitely generated nilpotent by finitely
--   generated free abelian, an isomorphism onto a discrete subgroup of a Lie group with finitely many
--   components, the same for a connected solvable Lie group, and a faithful representation by integer
--   matrices; they are not part of this mission.
-- source:
--   Wolf, J. A., Growth of finitely generated solvable groups and curvature of Riemannian manifolds, Journal of Differential Geometry 2 (1968) 421–446, https://doi.org/10.4310/jdg/1214428658, Proposition 4.1, conditions (1)–(7), p. 432–433

import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Wolf

theorem isPolycyclic_tfae {Γ : Type*} [Group Γ] [Group.IsSolvable Γ] :
    List.TFAE
      [ MilnorWolf.IsPolycyclic Γ,
        (∃ (u : ℕ) (B : Fin (u + 1) → Subgroup Γ), B 0 = ⊤ ∧ B (Fin.last u) = ⊥ ∧
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
        (∀ k : ℕ, ⁅derivedSeries Γ k, derivedSeries Γ k⁆ ≤ derivedSeries Γ (k + 1) ∧
          ∃ T : Finset Γ, derivedSeries Γ k = Subgroup.closure (T : Set Γ) ⊔ derivedSeries Γ (k + 1)),
        (∀ k : ℕ, Group.FG (derivedSeries Γ k)),
        (∀ H : Subgroup Γ, Group.FG H),
        WellFoundedGT (Subgroup Γ) ] := by
  sorry

end Wolf
