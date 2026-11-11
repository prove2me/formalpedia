-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_5_1
-- name    : ZeroFreeRRG.Hardcore.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:37:38.709296+00:00
-- url     : https://prove2.me/theorems/d376c21f-5174-49fe-8f55-1b4804def5cd
-- title:
--   Theorem 5.1 — under Conditions 1 and 2 at t, Z_G is zero-free on a fixed complex neighbourhood of t w.h.p. over 𝒢_{n,d}; also at α = 0, β = 1
-- statement:
--   Fix an integer $d\ge3$ and a nontrivial parameter $t$ for the hardcore or antiferromagnetic $q$-state Potts model ($q\ge2$). If Condition 1 and Condition 2 hold at $(d,t)$, then there is a fixed open set $U\ni t$ of complex parameters such that, with probability $1-o_n(1)$ over a uniformly random simple $d$-regular graph $G$ on $[n]$,
--   $$Z_G(z)\neq0\quad\text{for all }z\in U,$$
--   where $Z_G$ is the hardcore $Z_{G,\mathrm{fug}}(\lambda(\alpha))$ or the Potts $Z_{G,q}(\beta)$. The same conclusion holds at the independent-spin endpoints $\alpha=0$ and $\beta=1$.
--
--   Covering $[0,\alpha_{\mathrm{RSB}}(d)-\delta]$ by finitely many such neighbourhoods proves Theorem 1.2.
--
--   Differences from the source:
--   - encoding: 'the hardcore model (Ω = {0,1}) or the antiferromagnetic Potts model (Ω = [q], q ≥ 2)' → one statement over m : Model with m.Valid (q ≥ 2 for Potts); spins Fin 2 (0 = unoccupied) and Fin q; reason: states both printed cases at once; each instance m = .hardcore, m = .potts q is the source's case
--   - encoding: 'with probability 1 − o_n(1) over G ∼ 𝒢_{n,d}' (uniform simple d-regular graph on [n], admissible n) → the published PottsRapidMixing.WithHighProb d: the fraction of simple d-regular graphs on Fin n with the property tends to 1 along n with n·d even; reason: n ≥ d + 1 holds eventually; vertex set Fin n for [n]; constants are quantified outside the predicate, so they are chosen before n and G
--   - encoding: 'Z_G is zero-free on a fixed complex neighborhood of t' → ∃ U open with (t : ℂ) ∈ U, chosen before n and G (outside WithHighProb); reason: a neighbourhood contains an open one
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 37, Theorem 5.1

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional

open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- **Theorem 5.1** (zero-freeness under strict variational conditions; p. 37). Fix `d ≥ 3` and the
hardcore or antiferromagnetic `q`-state Potts model (`q ≥ 2`). If Conditions 1 and 2 hold at
`(d, t)` for a nontrivial parameter `t`, then there is a fixed open set `U ∋ t` of complex
parameters such that, with probability `1 − o_n(1)` over `G ∼ 𝒢_{n,d}`, `Z_G` has no zero in `U`.
The same holds at the independent-spin endpoint (`α = 0`, resp. `β = 1`). -/
theorem theorem_5_1 (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) :
    (∀ t : ℝ, m.Nontrivial t → Condition1 m d t → Condition2 m d t →
      ∃ U : Set ℂ, IsOpen U ∧ (t : ℂ) ∈ U ∧
        PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0)) ∧
    (∃ U : Set ℂ, IsOpen U ∧ ((m.indepEndpoint : ℝ) : ℂ) ∈ U ∧
        PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0)) := by sorry

end ZeroFreeRRG.Hardcore
