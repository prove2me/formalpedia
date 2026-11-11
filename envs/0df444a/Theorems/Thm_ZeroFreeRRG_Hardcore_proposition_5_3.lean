-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_proposition_5_3
-- name    : ZeroFreeRRG.Hardcore.proposition_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:38:53.687198+00:00
-- url     : https://prove2.me/theorems/96bdd63a-015f-47d6-ac24-e07d5107cc74
-- title:
--   Proposition 5.3 — first-moment Bethe upper bound: profile contributions exp{nΦ_s + O(log n)}; quadratic decay of Φ_s when κ_a(t) ≤ 0
-- statement:
--   Fix $d\ge3$ and the hardcore or $q$-state Potts model ($q\ge2$); expectations are under $\mathrm{CM}_{n,d}$.
--
--   (1) For real $s$ with $\pi(s)>0$ and $P(s)\ge0$, uniformly over all feasible profiles $(\rho,Q)$, the expected contribution to $\mathcal Z_G(s)$ from assignments with profile $(\rho,Q)$ is
--   $$\exp\{n\Phi_s(\rho,Q)+O_{d,|\Omega|}(\log n)\}\qquad(\text{equal to }0\text{ when }\Phi_s(\rho,Q)=-\infty).$$
--   (2) If $\kappa_a(t)\le0$ for all $a\ge2$, there is $c>0$ such that for every real $s$ near $t$ with $P(s)\ge0$ and every edge marginal $Q$ with vertex marginal $\rho$,
--   $$\Phi_s(\rho,Q)\le-c\big(\|\rho-\pi(s)\|_2^2+\|Q-P(s)\|_F^2\big),$$
--   and consequently $\log\mathbb E[\mathcal Z_G(s)]\le O(\log n)$.
--
--   It is the first-moment input of Lemma 5.5.
--
--   Differences from the source:
--   - encoding: 'the hardcore model (Ω = {0,1}) or the antiferromagnetic Potts model (Ω = [q], q ≥ 2)' → one statement over m : Model with m.Valid (q ≥ 2 for Potts); spins Fin 2 (0 = unoccupied) and Fin q; reason: states both printed cases at once; each instance m = .hardcore, m = .potts q is the source's case
--   - encoding: CM_{n,d}: the multigraph of a uniform perfect matching of the dn labelled half-edges → the published AFIsingKS.Matching n d (fixed-point-free involutions of Fin n × Fin d) with cmE / cmProb; edges are matched pairs, so self-loops and parallel edges are kept; reason: same probability space; products over E(G) run over edge occurrences via one half-edge per pair
--   - encoding: limits and 'for all sufficiently large n' along admissible n (n ≥ d + 1, dn even) → filter atTop ⊓ 𝓟 {n | Even (n * d)}, resp. ∃ N, ∀ n ≥ N with Even (n * d); reason: n ≥ d + 1 holds eventually, so the two index sets agree for all large n
--   - encoding: O(·) and 'for all large n' → explicit existential constants C (and N) placed after the objects the page lets them depend on; reason: standard meaning of the asymptotic notation
--   - encoding: D_KL with 0 log(0/q) = 0, p log(p/0) = +∞; Φ_s may equal −∞ → klDiv, rateFn valued in EReal (⊥ = −∞); reason: D_KL(ρ‖π(s)) is finite because π(s) > 0, so no ⊤ − ⊤ occurs
--   - encoding: nonconstant eigenvalues κ_2(t), …, κ_|Ω|(t) of K_t counted with algebraic multiplicity → the set m.nonconstEig t of eigenvalues of K_t on {f : π(t)ᵀ f = 0}; reason: only max_a |κ_a| and the signs κ_a ≤ 0 are used; these depend only on the set of values
--   - encoding: κ_a(t) ≤ 0 (real at real t) → κ ≤ 0 in the order of ℂ (scoped ComplexOrder): real and nonpositive; reason: the eigenvalues are real at real t (reversibility, p. 15), so this is the same condition
--   - encoding: 'exp{nΦ_s + O_{d,|Ω|}(log n)}' uniformly over s and feasible profiles → ∃ C N (chosen after the model and d only), ∀ s, ∀ admissible n ≥ N, ∀ feasible (ρ,Q): contribution > 0 and |log contribution − nΦ_s| ≤ C log n when Φ_s ≠ −∞; reason: O_{d,|Ω|} lets the constant depend only on d and |Ω|, which the model fixes
--   - reading: 'for every real s near t … and consequently log E[𝒵_G(s)] ≤ O(log n)' → ∃ c, ε, C, N with the bounds for every s ∈ (t − ε, t + ε) with P(s) ≥ 0; reason: one neighbourhood and constants uniform in s (the stronger reading); t is a nontrivial parameter by the §5.1 standing assumption
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 38, Proposition 5.3 (with Definition 5.2 and the §5.1 standing assumptions)

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments

open scoped Classical ComplexOrder

namespace ZeroFreeRRG.Hardcore

/-- **Proposition 5.3** (first-moment Bethe upper bound; p. 38), for `d ≥ 3` and the hardcore or
`q`-state Potts model (`q ≥ 2`), under `CM_{n,d}` along admissible `n`.
(1) There are constants `C, N` (depending only on `d` and the model, i.e. on `d` and `|Ω|`) such
that for every real `s` with `π(s) > 0` and `P(s) ≥ 0`, every `n ≥ N` with `dn` even and every
feasible profile `(ρ, Q)`, the expected contribution to `𝒵_G(s)` from assignments with profile
`(ρ, Q)` is `0` when `Φ_s(ρ, Q) = −∞`, and otherwise is positive with
`|log(contribution) − nΦ_s(ρ, Q)| ≤ C log n`.
(2) If `t` is a nontrivial parameter with `κ_a(t) ≤ 0` for all `a ≥ 2`, there are `c > 0` and a
neighbourhood `(t − ε, t + ε)` such that for every real `s` there with `P(s) ≥ 0` and every edge
marginal `Q` with vertex marginal `ρ`, `Φ_s(ρ, Q) ≤ −c(‖ρ − π(s)‖₂² + ‖Q − P(s)‖_F²)`, and
consequently `log E[𝒵_G(s)] ≤ C log n` for all admissible `n ≥ N`. -/
theorem proposition_5_3 (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) :
    (∃ C : ℝ, ∃ N : ℕ, ∀ s : ℝ, (∀ a, 0 < m.pi s a) → (∀ i j, 0 ≤ m.P s i j) →
      ∀ n ≥ N, Even (n * d) → ∀ (ρ : m.Spin → ℝ) (Q : m.Spin → m.Spin → ℝ), Feasible n d ρ Q →
        (rateFn d (m.pi s) (m.P s) ρ Q = ⊥ → profileContribution m s d n ρ Q = 0) ∧
        (rateFn d (m.pi s) (m.P s) ρ Q ≠ ⊥ → 0 < profileContribution m s d n ρ Q ∧
          |Real.log (profileContribution m s d n ρ Q) -
              n * (rateFn d (m.pi s) (m.P s) ρ Q).toReal| ≤ C * Real.log n)) ∧
    (∀ t : ℝ, m.Nontrivial t → (∀ κ ∈ m.nonconstEig (t : ℂ), κ ≤ 0) →
      ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ N : ℕ,
        ∀ s : ℝ, |s - t| < ε → (∀ i j, 0 ≤ m.P s i j) →
          (∀ (ρ : m.Spin → ℝ) (Q : m.Spin → m.Spin → ℝ), IsEdgeMarginal ρ Q →
            rateFn d (m.pi s) (m.P s) ρ Q ≤
              (((-c) * sqDist ρ (m.pi s) Q (m.P s) : ℝ) : EReal)) ∧
          ∀ n ≥ N, Even (n * d) → Real.log (an m d n s) ≤ C * Real.log n) := by sorry

end ZeroFreeRRG.Hardcore
