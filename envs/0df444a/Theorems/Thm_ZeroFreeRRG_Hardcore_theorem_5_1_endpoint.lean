-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_5_1_endpoint
-- name    : ZeroFreeRRG.Hardcore.theorem_5_1_endpoint
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:26:32.385192+00:00
-- url     : https://prove2.me/theorems/87c2a029-f796-4e90-8d32-da1ee4d997b7
-- title:
--   Independent-spin endpoint of zero-freeness
-- statement:
--   Fix $d\ge3$ and either the hardcore model or the antiferromagnetic $q$-state Potts model with $q\ge2$. Let $t_0=0$ for the hardcore model and $t_0=1$ for the Potts model. There exists an open complex neighborhood $U$ of $t_0$ such that
--
--   $$\Pr_{G\sim\mathcal G_{n,d}}[Z_G(z)\ne0\text{ for all }z\in U]\longrightarrow1$$
--
--   as $n\to\infty$ along admissible values with $nd$ even. This is the independent-spin endpoint part of Theorem 5.1.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://arxiv.org/abs/2610.40510, Theorem 5.1, p. 37; stated conjunct of theorem.

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore
theorem theorem_5_1_endpoint (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) :
    ∃ U : Set ℂ, IsOpen U ∧ ((m.indepEndpoint : ℝ) : ℂ) ∈ U ∧
        PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0) := by sorry
end ZeroFreeRRG.Hardcore
