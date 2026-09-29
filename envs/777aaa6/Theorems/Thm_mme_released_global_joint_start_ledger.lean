-- Prove2me | Theorems.Thm_mme_released_global_joint_start_ledger
-- name    : mme_released_global_joint_start_ledger
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T15:26:16.010261+00:00
-- url     : https://prove2.me/theorems/1e415cc2-17d6-4cd9-b75f-e05d4a8d0d89
-- title:
--   Quantitative assembly of global Parts and a joint continuation
-- statement:
--   Let $B=D^5k$, $n=6B$, and let six physical Parts satisfy the certified regional bounds $\rho_oB+\log U_o\leq r_o$ and $1\leq U_o\leq(B+1)^{10935}$. Let $R$ be a logarithmic joint recipe on their entire interface, with $U_R\geq1$ and
--   $$n\rho+\log U_R\leq L_R.$$
--   The explicit combined Start $A$ has the same three matrix dimensions as $R$ and satisfies
--   $$1\leq U_A\leq(B+1)^{65610}U_R,\qquad
--   n\left(\frac{2235998128}{1500000000}+\rho\right)+\log U_A\leq L_A.$$
--   The global contribution is the average of six separately certified rates, with the explicit $10^{-8}$ reserve already deducted. The logarithms account for all global and recursive input copies.
-- source:
--   Auxiliary formalization for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2, Theorem 5.3, Section 5.1, Theorem 6.4 and Algorithm 1. Specialization to the published exact ReleasedGlobal seed; the numerical recursive continuation remains an explicit separate obligation.

import Definitions.Def_mme_released_global_joint_interface
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
universe u

theorem mme_released_global_joint_start_ledger (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ)
    (S : ∀ o, Part (4 * blocks k) 3 (physicalWindow o k hk (a o) (eps o)))
    (hS : ∀ o, 1 ≤ (S o).inputs ∧ (S o).inputs ≤ (blocks k+1)^10935 ∧
      usableRate o * (blocks k : ℝ) + Real.log ((S o).inputs : ℝ) ≤ (S o).rate)
    (R : LogJointRecipe (4 * (6 * blocks k)) 3 (jointWindow k hk a eps))
    (hR : 1 ≤ R.inputs) (rho : ℝ)
    (hrate : (6 * blocks k : ℕ) * rho + Real.log (R.inputs : ℝ) ≤ R.logOutputs) :
    let D := jointStart k hk a eps S R
    1 ≤ D.inputs ∧ D.inputs ≤ (blocks k+1)^65610 * R.inputs ∧
      D.a = R.a ∧ D.b = R.b ∧ D.c = R.c ∧
      (6 * blocks k : ℕ) * ((2235998128 : ℝ)/1500000000 + rho) +
        Real.log (D.inputs : ℝ) ≤ D.logOutputs := by sorry
