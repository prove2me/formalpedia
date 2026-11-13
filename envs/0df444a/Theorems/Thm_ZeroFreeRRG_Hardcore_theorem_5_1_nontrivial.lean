-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_5_1_nontrivial
-- name    : ZeroFreeRRG.Hardcore.theorem_5_1_nontrivial
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:26:39.606518+00:00
-- url     : https://prove2.me/theorems/06c98554-7f66-4e1b-a35c-794bb9a56304
-- title:
--   Zero-freeness under strict variational conditions at nontrivial parameters
-- statement:
--   Fix $d\ge3$, either the hardcore model or the antiferromagnetic $q$-state Potts model with $q\ge2$, and a nontrivial real parameter $t$. If the two variational Conditions 1 and 2 of the paper hold at $(d,t)$, then there exists an open complex neighborhood $U$ of $t$ such that
--
--   $$\Pr_{G\sim\mathcal G_{n,d}}[Z_G(z)\ne0\text{ for all }z\in U]\longrightarrow1$$
--
--   as $n\to\infty$ along admissible values with $nd$ even. This is the nontrivial-parameter part of Theorem 5.1.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://arxiv.org/abs/2610.40510, Theorem 5.1, p. 37; stated conjunct of theorem.

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore
theorem theorem_5_1_nontrivial (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) :
    ∀ t : ℝ, m.Nontrivial t → Condition1 m d t → Condition2 m d t →
      ∃ U : Set ℂ, IsOpen U ∧ (t : ℂ) ∈ U ∧
        PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0) := by sorry
end ZeroFreeRRG.Hardcore
