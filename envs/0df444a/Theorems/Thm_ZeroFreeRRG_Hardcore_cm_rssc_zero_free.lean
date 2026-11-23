-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cm_rssc_zero_free
-- name    : ZeroFreeRRG.Hardcore.cm_rssc_zero_free
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:23:28.029656+00:00
-- url     : https://prove2.me/theorems/5cfc9980-cf16-4ed4-ad24-8f2423774d6d
-- title:
--   RSSC gives normalized zero-freeness on simple configuration-model graphs
-- statement:
--   Fix $d\ge3$, the hardcore model or the $q$-state antiferromagnetic Potts model with $q\ge2$, and a nontrivial real parameter $t$ satisfying Conditions 1 and 2. There is $R>0$ such that, under $\mathrm{CM}_{n,d}$ along admissible $n$,
--   $$
--   \Pr\big[\text{if }G\text{ is simple, then }\mathcal Z_G(z)\ne0\text{ for every }z\in\overline D(t,R)\big]\longrightarrow1.
--   $$
--   This is the configuration-model conclusion of the proof of Theorem 5.1: Lemmas 4.21 and 5.5 verify (B0)–(B5) for the truncated normalized partition function, Theorem 3.2 gives zero-freeness conditionally on $X_{1,n}=X_{2,n}=0$, and simplicity then forces the truncation event. The statement packages that argument without yet passing to the Bethe canonical form or to uniform simple regular graphs.
--
--   **Formalization Note.** `normZ` is $\mathcal Z_G$, `IsSimpleM` is simplicity of the pairing, and the convergence is along $n$ with $nd$ even.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510, proof of Theorem 5.1, p. 40 (PDF p. 41), §5.3; uses Theorem 3.2 pp. 18–19, Lemma 4.21 p. 32 and Lemma 5.5 p. 39.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel

open scoped Classical
open Filter Topology AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- Configuration-model consequence of RSSC, the truncation lemma, and the local moment estimates:
on a fixed closed complex disk about a nontrivial parameter satisfying Conditions 1 and 2, the
normalized partition function is zero-free on simple configuration-model graphs with probability
tending to one. -/
theorem cm_rssc_zero_free (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ)
    (ht : m.Nontrivial t) (hC1 : Condition1 m d t) (hC2 : Condition2 m d t) :
    ∃ R : ℝ, 0 < R ∧
      Tendsto (fun n => cmProb (fun M : Matching n d => IsSimpleM M →
        ∀ z ∈ Metric.closedBall (t : ℂ) R, normZ m z M ≠ 0))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1) := by sorry
