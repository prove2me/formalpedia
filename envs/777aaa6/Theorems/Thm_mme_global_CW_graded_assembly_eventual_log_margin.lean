-- Prove2me | Theorems.Thm_mme_global_CW_graded_assembly_eventual_log_margin
-- name    : mme_global_CW_graded_assembly_eventual_log_margin
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-30T08:54:58.867993+00:00
-- url     : https://prove2.me/theorems/bf955a80-a6d8-4845-89b7-3fadabc151f3
-- title:
--   Graded global assembly preserves a strict rate surplus beyond a uniform scale
-- statement:
--   Fix a block size $b$, a level $\ell$, a number $p$ of global parts, and a polynomial degree $d$. Let $G,R,V,\tau$ be real numbers with $\tau\ge0$ and
--
--   $$b\log 7<G+R+\tau V.$$
--
--   All logarithms are natural. There is a threshold $k_0$, depending only on these constants, with the following property. For every $k\ge k_0$ and $n\ge k^2$, suppose the $bn$ positions are partitioned into $p$ parts. On each part provide an actual global extraction stage $S_j$, with target predicate $T_j$. Provide a whole-interface predicate $Q$ implying all part targets, and a graded regional continuation $C$ of level $\ell$ on $Q$.
--
--   Assume
--
--   $$1\le U(S_j)\le(k+1)^d,\qquad 1\le U(C)\le(k+1)^d,\qquad 1\le a_Cb_Cc_C,$$
--
--   and the rate bounds
--
--   $$nG\le\sum_j L(S_j),\qquad nR\le L(C),\qquad nV\le\log(a_Cb_Cc_C).$$
--
--   Then these components assemble into a graded global start $D$ on $bn$ positions with $n>0$, positive input and matrix-volume counts, and
--
--   $$\log U(D)+bn\log7<L(D)+\tau\log(a_Db_Dc_D).$$
--
--   The threshold is uniform in the physical partition, predicates, and extraction components. The components carry their actual finite extraction and interface obligations. Their existence is a hypothesis, not a consequence of a numerical rate inequality alone.
--
--   For the AlphaEvolve mission, take $b=8$, $\ell=4$, $p=6$, and $\tau=2371177/3000000$. This auxiliary assembly result does not supply the witness-specific components or numerical rates.
-- source:
--   Auxiliary theorem derived directly from the platform definitions of GlobalCW.StartG and its inputs, logOutputs, and dimensions, https://prove2.me/theorems/4002300c-bb1c-49e3-809b-d36575573129, and GlobalCW.Part, https://prove2.me/theorems/cad730ba-f243-4430-95f8-5ad297586a89. Application context: Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, arXiv:2608.16884v1, Section 2.4 (final assembly), https://arxiv.org/html/2608.16884v1#S2.SS4. This auxiliary theorem is not stated verbatim in that paper.

import Definitions.Def_mme_global_CW_graded_start_data
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RegionRealization
set_option autoImplicit false

theorem mme_global_CW_graded_assembly_eventual_log_margin
    (blockSize ell parts degree : ℕ) (globalRate regionalRate volumeRate tau : ℝ)
    (htau : 0 ≤ tau)
    (hgap : (blockSize : ℝ) * Real.log 7 <
      globalRate + regionalRate + tau * volumeRate) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ n : ℕ, k ^ 2 ≤ n →
      ∀ (size : Fin parts → ℕ)
        (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin (blockSize * n))
        (T : ∀ j, Predicate (size j))
        (steps : ∀ j, GlobalCW.Part (size j) ell (T j))
        (Q : Predicate (blockSize * n))
        (target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j, r⟩)))
        (next : LogJointRecipeG (blockSize * n) ell Q),
      (∀ j, 1 ≤ (steps j).inputs ∧ (steps j).inputs ≤ (k + 1) ^ degree) →
      1 ≤ next.inputs → next.inputs ≤ (k + 1) ^ degree →
      1 ≤ next.a * next.b * next.c →
      (n : ℝ) * globalRate ≤ ∑ j, (steps j).rate →
      (n : ℝ) * regionalRate ≤ next.logOutputs →
      (n : ℝ) * volumeRate ≤ Real.log ((next.a * next.b * next.c : ℕ) : ℝ) →
      ∃ D : GlobalCW.StartG (blockSize * n) ell,
        0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
        Real.log (D.inputs : ℝ) + ((blockSize * n : ℕ) : ℝ) * Real.log 7 <
          D.logOutputs + tau * Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by sorry
