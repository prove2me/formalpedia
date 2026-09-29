-- Prove2me | Theorems.Thm_mme_stothers_phi233_isolated_kept_profile_value
-- name    : mme_stothers_phi233_isolated_kept_profile_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:10:52.342382+00:00
-- url     : https://prove2.me/theorems/42e8521e-6038-4bf0-8c04-21f5e7a7e051
-- title:
--   A retained $\Phi_{233}$ family transfers uniform profile value to the source power
-- statement:
--   Fix an isolated, mode-disjoint retained family $S$ of exact $\Phi_{233}$ cyclic profile edges. Suppose the common ten-component profile tensor carried by every edge has $\tau$-value at least every nonnegative number strictly below $B$. Then the $(2N)$-th tensor power of the cyclic $\Phi_{233}$ constituent has $\tau$-value at least every nonnegative $V$ satisfying
--
--   $$
--   V<|S|B.
--   $$
--
--   The result combines the literal tensor restriction for the retained family with additivity of weighted volume across a finite direct sum. It is the value-theoretic interface used after the asymmetric hashing step has produced a large retained family.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), induced direct-sum value aggregation in Lemma 3.3 and the exceptional phi_233 application in Lemma 5.1(v), pp. 356--360 and 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Definitions.Def_mme_stothers_phi233_outer_grading
import Definitions.Def_mme_CW_2376_address_block
import Theorems.Thm_mme_stothers_phi233_isolated_kept_profile_product_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_isolated_kept_profile_value
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (kept : Finset
      (MME.StothersFourth.Phi233.CyclicAmbientEdge
        N alpha beta gamma delta))
    (hkept : kept ⊆
      MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta)
    (hisolated :
      ∀ e ∈ MME.StothersFourth.Phi233.ambientFinset
          N alpha beta gamma delta,
        (∀ i : Fin 3, ∃ f ∈ kept,
          MME.StothersFourth.Phi233.cyclicModeWord e i =
            MME.StothersFourth.Phi233.cyclicModeWord f i) →
        e ∈ kept)
    (hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦
        MME.StothersFourth.Phi233.cyclicModeWord e.1 i))
    (tau B : ℝ) (hB : 0 ≤ B)
    (hprofile : ∀ W : ℝ, 0 ≤ W → W < B →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (TensorObj.kronFin 10 (fun r ↦
            (MME.StothersFourth.Phi233.componentObj K q r).kronPow
              (MME.StothersFourth.Phi233.profileMultiplicity
                alpha beta gamma delta r)))) tau W)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < (kept.card : ℝ) * B) :
    HasTauValueAtLeast
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K q 2 3 3)).kronPow
          (2 * N)) tau V := by
  sorry
