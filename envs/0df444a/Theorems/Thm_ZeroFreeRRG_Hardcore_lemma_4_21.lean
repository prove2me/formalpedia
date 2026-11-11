-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_21
-- name    : ZeroFreeRRG.Hardcore.lemma_4_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:38:59.675573+00:00
-- url     : https://prove2.me/theorems/0ae6a8f6-b1bb-4fe7-87ac-1c72b8a7f1cb
-- title:
--   Lemma 4.21 — typical-graph truncation Y_n = 𝒵_G 1{E_n} matches the first and local second moments up to e^{−γn}
-- statement:
--   Fix $d\ge3$ and the hardcore or $q$-state Potts model ($q\ge2$); expectations are under $\mathrm{CM}_{n,d}$. Assume Conditions 1 and 2 hold at a nontrivial parameter $t$. For a sufficiently small overlap box $B$ about $\pi(t)\otimes\pi(t)$ there exist graph events $E_n$, an open disk $D_0$ about $t$, and $\gamma>0$ such that
--   $$\mathbb E\big[(\mathcal Z_G(t)^2-\mathcal Z^{(2)}_{G,B}(t,t))\mathbf 1\{E_n\}\big]=O(e^{-\gamma n}a_n(t)^2)$$
--   and, uniformly for $z,w\in D_0$, with $Y_n(z)=\mathcal Z_G(z)\mathbf 1\{E_n\}$,
--   $$\mathbb E[Y_n(z)]=a_n(z)\big(1+O(e^{-\gamma n})\big),\qquad \mathbb E[Y_n(z)Y_n(w)]=\mathbb E[\mathcal Z^{(2)}_{G,B}(z,w)]+O\big(e^{-\gamma n}|a_n(z)a_n(w)|\big).\tag{31}$$
--   It supplies the random holomorphic functions $Y_n$ to which Theorem 3.2 is applied.
--
--   Differences from the source:
--   - encoding: 'the hardcore model (Ω = {0,1}) or the antiferromagnetic Potts model (Ω = [q], q ≥ 2)' → one statement over m : Model with m.Valid (q ≥ 2 for Potts); spins Fin 2 (0 = unoccupied) and Fin q; reason: states both printed cases at once; each instance m = .hardcore, m = .potts q is the source's case
--   - encoding: CM_{n,d}: the multigraph of a uniform perfect matching of the dn labelled half-edges → the published AFIsingKS.Matching n d (fixed-point-free involutions of Fin n × Fin d) with cmE / cmProb; edges are matched pairs, so self-loops and parallel edges are kept; reason: same probability space; products over E(G) run over edge occurrences via one half-edge per pair
--   - encoding: limits and 'for all sufficiently large n' along admissible n (n ≥ d + 1, dn even) → filter atTop ⊓ 𝓟 {n | Even (n * d)}, resp. ∃ N, ∀ n ≥ N with Even (n * d); reason: n ≥ d + 1 holds eventually, so the two index sets agree for all large n
--   - reading: 'for every sufficiently small (open) overlap box B around π(t) ⊗ π(t)'; a box is the preimage of an open axis-aligned box in |Ω|² − 1 coordinates of Δ_{Ω×Ω} → ∃ r > 0 such that for every dropped coordinate c₀ and corners lo, hi with π(t)⊗π(t) ∈ overlapBox c₀ lo hi and all side lengths hi − lo < r, the conclusion holds; reason: 'sufficiently small' = below some size every such box works; every choice of the dropped coordinate is covered (the stronger reading)
--   - encoding: an open (complex) disk D₀ about t → Metric.ball (t : ℂ) R with R > 0; reason: same set
--   - encoding: O(·) and 'for all large n' → explicit existential constants C (and N) placed after the objects the page lets them depend on; reason: standard meaning of the asymptotic notation
--   - encoding: graph events E_n → E n : Set (Matching n d) with IsGraphEvent (E n): a set of pairings that depends only on the induced multigraph; reason: an event of the configuration-model multigraph G is a set of pairings closed under relabelling the half-edges that induce the same G
--   - encoding: O(e^{−γn} a_n(t)²) and a_n(z)(1 + O(e^{−γn})) → ‖·‖ ≤ C e^{−γn} ‖a_n(t)‖², ‖E[Y_n(z)] − a_n(z)‖ ≤ C e^{−γn} ‖a_n(z)‖ for admissible n ≥ N, one C for all z, w ∈ D₀; reason: the page's 'uniformly for z, w ∈ D₀'; a_n(t) is real and positive
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 32, Lemma 4.21 (with eq. (30) and the §4.3 setting)

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical
open AFIsingKS

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 4.21** (p. 32), for `d ≥ 3` and the hardcore or `q`-state Potts model (`q ≥ 2`), under
`CM_{n,d}` along admissible `n`. Assume Conditions 1 and 2 at a nontrivial parameter `t`. There is a
size `r > 0` such that for every overlap box `B` about `π(t) ⊗ π(t)` with side lengths `< r` there
exist graph events `E_n`, an open disk `D₀` about `t` and `γ > 0` with
`E[(𝒵_G(t)² − 𝒵^{(2)}_{G,B}(t, t)) 1{E_n}] = O(e^{−γn} a_n(t)²)` and, uniformly for `z, w ∈ D₀`,
(31) `E[Y_n(z)] = a_n(z)(1 + O(e^{−γn}))` and
`E[Y_n(z) Y_n(w)] = E[𝒵^{(2)}_{G,B}(z, w)] + O(e^{−γn} |a_n(z) a_n(w)|)`, where
`Y_n = 𝒵_G 1{E_n}`. Each `O(·)` is a constant `C` valid for all admissible `n ≥ N`. -/
theorem lemma_4_21 (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.Nontrivial t)
    (hC1 : Condition1 m d t) (hC2 : Condition2 m d t) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
      tensorVec (m.pi t) (m.pi t) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
      ∃ E : ∀ n : ℕ, Set (Matching n d), (∀ n, IsGraphEvent (E n)) ∧
        ∃ R : ℝ, 0 < R ∧ ∃ γ : ℝ, 0 < γ ∧
        ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
          ‖cmE (fun M : Matching n d =>
              if M ∈ E n then normZ m (t : ℂ) M ^ 2 - Z2 m (overlapBox c₀ lo hi) t t M else 0)‖
            ≤ C * Real.exp (-γ * n) * ‖an m d n (t : ℂ)‖ ^ 2 ∧
          ∀ z ∈ Metric.ball (t : ℂ) R, ∀ w ∈ Metric.ball (t : ℂ) R,
            ‖cmE (fun M : Matching n d => if M ∈ E n then normZ m z M else 0) - an m d n z‖
              ≤ C * Real.exp (-γ * n) * ‖an m d n z‖ ∧
            ‖cmE (fun M : Matching n d =>
                (if M ∈ E n then normZ m z M else 0) * (if M ∈ E n then normZ m w M else 0)) -
              cmE (fun M : Matching n d => Z2 m (overlapBox c₀ lo hi) z w M)‖
              ≤ C * Real.exp (-γ * n) * ‖an m d n z * an m d n w‖ := by sorry

end ZeroFreeRRG.Hardcore
