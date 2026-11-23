-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_rsscCond
-- name    : ZeroFreeRRG.Hardcore.rsscCond
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:41:14.15489+00:00
-- url     : https://prove2.me/theorems/36bb60cf-8608-4918-b80a-e88805ef187b
-- title:
--   Conditional zero-freeness of the truncated configuration-model partition function
-- statement:
--   Fix $d\ge3$ and the hardcore model or the $q$-state antiferromagnetic Potts model with $q\ge2$. Let $t$ be a nontrivial real parameter satisfying Conditions 1 and 2. There are $R>0$ and graph events $E_n$ such that $Y_n(z)=\mathcal Z_G(z)\mathbf 1\{E_n\}$ satisfies
--   $$
--   \Pr_{\mathrm{CM}_{n,d}}\!\left[Y_n(z)\ne0\text{ for every }z\in\overline D(t,R)
--   \ \middle|\ X_{1,n}=X_{2,n}=0\right]\longrightarrow1
--   $$
--   along admissible $n$ with $nd$ even.
--
--   This packages the central application in the proof of Theorem 5.1. Lemma 4.21 supplies the graph truncation, Lemma 5.5 supplies the local first and second moments and cycle factors used to verify (B0)–(B5), and Theorem 3.2 then gives zero-freeness of $Y_n$ on a compact disk after conditioning on the first two cycle counts vanishing.
--
--   **Formalization Note.** `cmCondProb` is the finite uniform conditional probability. Each $E_n$ is a graph event: it depends only on the induced multigraph, not on half-edge labels. The normalized partition function is $\mathcal Z_G$, and $\overline D(t,R)$ is `Metric.closedBall (t : ℂ) R`.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510, proof of Theorem 5.1, p. 40 (PDF p. 41), second and third paragraphs; Theorem 3.2 pp. 18–19, Lemma 4.21 p. 32 and Lemma 5.5 p. 39.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_CMCond

open scoped Classical
open Filter Topology AFIsingKS

/-- The configuration-model application of reinforced small subgraph conditioning. For a
nontrivial parameter satisfying Conditions 1 and 2, the truncation supplied by Lemma 4.21,
with the local estimates of Lemma 5.5, is zero-free on a fixed closed disk with conditional
probability tending to one given the absence of loops and parallel edges. -/
theorem ZeroFreeRRG.Hardcore.rsscCond (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ)
    (ht : m.Nontrivial t) (hC1 : Condition1 m d t) (hC2 : Condition2 m d t) :
    ∃ R : ℝ, 0 < R ∧ ∃ E : ∀ n : ℕ, Set (Matching n d), (∀ n, IsGraphEvent (E n)) ∧
      Tendsto (fun n => cmCondProb
        (fun M : Matching n d => cycleCount M 1 = 0 ∧ cycleCount M 2 = 0)
        (fun M => ∀ z ∈ Metric.closedBall (t : ℂ) R,
          (if M ∈ E n then normZ m z M else 0) ≠ 0))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1) := by sorry
