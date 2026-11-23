-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cm_simple_to_regular
-- name    : ZeroFreeRRG.Hardcore.cm_simple_to_regular
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:26:18.150585+00:00
-- url     : https://prove2.me/theorems/7d03657f-546f-4f1d-a287-c55da47a063c
-- title:
--   Transfer a simple-CM high-probability event to uniform regular graphs
-- statement:
--   Let $U\subseteq\mathbb C$ and fix $d\ge3$. Suppose that, under $\mathrm{CM}_{n,d}$ along admissible $n$, the probability tends to one that every simple pairing has contracted graph $G$ satisfying $Z_G(z)\ne0$ for all $z\in U$. Then the same zero-freeness property holds with probability $1-o_n(1)$ for a uniform simple $d$-regular graph on $[n]$.
--
--   The transfer uses the two standard facts in Definitions 2.2 and Lemma 2.3: conditioned on simplicity the configuration model is uniform on simple $d$-regular graphs, and its simplicity probability is bounded below by a positive constant. No property of the particular spin model is used.
--
--   **Formalization Note.** `cmProb (IsSimpleM M → …)` is one minus the configuration-model probability of a simple pairing violating the desired property; the uniformity and positive-simplicity-probability inputs convert this into convergence of `PottsRapidMixing.regularProb` to one.
-- source:
--   Chen, Wang, Zhang, arXiv:2610.40510, p. 16, Definition 2.2 and Lemma 2.3; final conditioning step in the proof of Theorem 5.1, p. 40.

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_Models

open scoped Classical
open Filter Topology AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- A property of the contracted simple graph that holds with asymptotic probability one under the
configuration model also holds with asymptotic probability one under the uniform simple `d`-regular
graph law. -/
theorem cm_simple_to_regular (m : Model) (d : ℕ) (hd : 3 ≤ d) (U : Set ℂ)
    (h : Tendsto (fun n => cmProb (fun M : Matching n d => IsSimpleM M →
        ∀ z ∈ U, m.Zgraph d (toGraph M) z ≠ 0))
      (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1)) :
    PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0) := by sorry
