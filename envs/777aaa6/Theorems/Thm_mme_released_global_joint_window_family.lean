-- Prove2me | Theorems.Thm_mme_released_global_joint_window_family
-- name    : mme_released_global_joint_window_family
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T15:25:38.046626+00:00
-- url     : https://prove2.me/theorems/deb70187-c4cb-489d-9305-a1ebcd7f3816
-- title:
--   Simultaneous physical global windows on a common square scale
-- statement:
--   Write $D=10^{12}$ and $B(t)=D^5t$. For each owner $o$, set $\rho_o=f_o-10^{-8}$, where $f_o$ is its previously proved rational rate floor. Given any six positive tolerance caps $\eta_o$, there are fixed positive tolerances $\varepsilon_o\leq\eta_o$ and a common threshold $k_0$ such that every integer $k\geq k_0$ admits references and physical global Parts $S_o$ on $4B(k^2)$ positions satisfying
--   $$1\leq U_o\leq(B(k^2)+1)^{10935},\qquad \rho_o B(k^2)+\log U_o\leq\operatorname{rate}(S_o),$$
--   where $U_o$ is the input count of $S_o$. All six Parts occur at the same square scale; their tolerances are chosen before that scale.
-- source:
--   Auxiliary formalization for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2, Theorem 5.3, Section 5.1, Theorem 6.4 and Algorithm 1. Specialization to the published exact ReleasedGlobal seed; the numerical recursive continuation remains an explicit separate obligation.

import Definitions.Def_mme_released_global_joint_interface
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
universe u

theorem mme_released_global_joint_window_family (eta : Fin 6 → ℝ) (heta : ∀ o, 0 < eta o) :
    ∃ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) ∧ (∀ o, eps o ≤ eta o) ∧
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ hk : 0 < k^2,
      ∃ a : ∀ o : Fin 6, Reference o (k^2),
      ∃ S : ∀ o, Part (4 * blocks (k^2)) 3 (physicalWindow o (k^2) hk (a o) (eps o)),
        ∀ o, 1 ≤ (S o).inputs ∧ (S o).inputs ≤ (blocks (k^2)+1)^10935 ∧
          usableRate o * (blocks (k^2) : ℝ) + Real.log ((S o).inputs : ℝ) ≤
            (S o).rate := by sorry
