-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_endpoint_zero_free
-- name    : ZeroFreeRRG.Hardcore.hardcore_endpoint_zero_free
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:05:46.7936+00:00
-- url     : https://prove2.me/theorems/4ccaeabe-a4e0-487f-aa92-d800ae6aee11
-- title:
--   Hardcore zero-freeness at the independent-spin endpoint
-- statement:
--   For each integer $d\ge3$ there exists an open complex neighborhood $U$ of $0$ such that
--
--   $$\Pr_{G\sim\mathcal G_{n,d}}[Z_G(\alpha)\ne0\text{ for every }\alpha\in U]\longrightarrow1$$
--
--   as $n\to\infty$ along admissible values. Here $Z_G(\alpha)$ is the hardcore partition function in the paper's occupation-density parameter. This is the hardcore independent-spin endpoint of Theorem 5.1.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Theorem 5.1 and Lemma 5.7, printed pp. 37 and 40.

import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- The hardcore independent-spin endpoint in Theorem 5.1. -/
theorem hardcore_endpoint_zero_free (d : ℕ) (hd : 3 ≤ d) :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, hardcoreZ d G z ≠ 0) := by sorry
end ZeroFreeRRG.Hardcore
