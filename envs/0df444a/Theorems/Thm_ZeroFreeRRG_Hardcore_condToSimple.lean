-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_condToSimple
-- name    : ZeroFreeRRG.Hardcore.condToSimple
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:42:00.686009+00:00
-- url     : https://prove2.me/theorems/fc6bf72b-ca6e-430a-a91a-f0d9797b853b
-- title:
--   Removing the first-two-cycle conditioning from truncated zero-freeness
-- statement:
--   Let $Y_n(z)=\mathcal Z_G(z)\mathbf 1\{E_n\}$ for arbitrary events $E_n$, and let $R>0$. Identify simplicity with $X_{1,n}=X_{2,n}=0$. If
--   $$
--   \Pr_{\mathrm{CM}_{n,d}}\!\left[Y_n\text{ has no zero on }\overline D(t,R)
--   \ \middle|\ X_{1,n}=X_{2,n}=0\right]\longrightarrow1,
--   $$
--   then also
--   $$
--   \Pr_{\mathrm{CM}_{n,d}}\!\left[G\text{ simple}\Longrightarrow
--   \mathcal Z_G(z)\ne0\text{ for every }z\in\overline D(t,R)\right]\longrightarrow1
--   $$
--   along admissible $n$.
--
--   The point is the last sentence of the proof of Theorem 5.1: since $Y_n\equiv0$ on $E_n^{\mathsf c}$ and the disk is nonempty, zero-freeness of $Y_n$ forces $E_n$. On $E_n$, $Y_n=\mathcal Z_G$, so the original normalized partition function is zero-free. Away from simplicity the implication in the conclusion holds automatically. This is a finite-probability transport lemma, independent of the particular truncation events.
--
--   **Formalization Note.** No graph-event hypothesis on $E_n$ is needed for this probability step. The only analytic input is $R>0$, which ensures that the closed disk contains $t$.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510, proof of Theorem 5.1, p. 40 (PDF p. 41), final sentence: 'Since Y_n ≡ 0 on E_n^c, this forces E_n, on which ...'.

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_CMCond

open scoped Classical
open Filter Topology AFIsingKS

/-- Removing the simplicity conditioning in the final step of the configuration-model
argument. Off the simplicity event the requested implication is automatic; on that event,
zero-freeness of the truncated function forces the truncation event and hence zero-freeness
of the original normalized partition function. -/
theorem ZeroFreeRRG.Hardcore.condToSimple (m : Model) (d : ℕ) (t : ℝ) (R : ℝ) (hR : 0 < R)
    (E : ∀ n : ℕ, Set (Matching n d))
    (hsimple : ∀ {n : ℕ} (M : Matching n d),
      IsSimpleM M ↔ cycleCount M 1 = 0 ∧ cycleCount M 2 = 0)
    (hcond : Tendsto (fun n => cmCondProb
        (fun M : Matching n d => cycleCount M 1 = 0 ∧ cycleCount M 2 = 0)
        (fun M => ∀ z ∈ Metric.closedBall (t : ℂ) R,
          (if M ∈ E n then normZ m z M else 0) ≠ 0))
        (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1)) :
    Tendsto (fun n => cmProb (fun M : Matching n d => IsSimpleM M →
      ∀ z ∈ Metric.closedBall (t : ℂ) R, normZ m z M ≠ 0))
      (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1) := by sorry
