-- Prove2me | Theorems.Thm_mme_released_global_joint_window_extraction
-- name    : mme_released_global_joint_window_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T15:25:33.29232+00:00
-- url     : https://prove2.me/theorems/3058065f-df17-4fff-a4ef-a4975c1eac2a
-- title:
--   Tensor extraction onto the whole six-region interface
-- statement:
--   Let $S_o$ be six physical global Parts at one scale, with input counts $U_o$ and logarithmic output rates $r_o$. Let $Q$ be the published joint-window predicate obtained by imposing each regional window on its own positions. Over every field, there exists an integer $V$ such that
--   $$e^{\sum_o r_o}\leq V,\qquad
--   \bigoplus_{V} T(Q)\ \preceq\ \bigoplus_{\prod_o U_o}\mathrm{CW}_5^{\otimes 24B}.$$
--   Here $B$ is the common regional block count and $\preceq$ denotes actual tensor restriction. This is the whole interface on which a joint recursive recipe can act.
-- source:
--   Auxiliary formalization for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2, Theorem 5.3, Section 5.1, Theorem 6.4 and Algorithm 1. Specialization to the published exact ReleasedGlobal seed; the numerical recursive continuation remains an explicit separate obligation.

import Definitions.Def_mme_released_global_joint_interface
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
universe u

theorem mme_released_global_joint_window_extraction {K : Type u} [Field K] (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ)
    (S : ∀ o, Part (4 * blocks k) 3 (physicalWindow o k hk (a o) (eps o))) :
    ∃ outputs : ℕ, Real.exp (∑ o, (S o).rate) ≤ (outputs : ℝ) ∧
      Restrict (bigAdd (fun _ : Fin outputs ↦ tensor K (jointWindow k hk a eps)))
        (bigAdd (fun _ : Fin (∏ o, (S o).inputs) ↦
          (CWObj K 5).kronPow (4 * (6 * blocks k)))) := by sorry
