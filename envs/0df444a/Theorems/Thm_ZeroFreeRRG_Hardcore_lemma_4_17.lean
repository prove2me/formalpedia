-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_17
-- name    : ZeroFreeRRG.Hardcore.lemma_4_17
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T21:37:24.104189+00:00
-- url     : https://prove2.me/theorems/016c5487-cdbf-42c6-a6d3-500960c0726d
-- title:
--   Lemma 4.17 — interior of the variational replica-symmetric regime implies Conditions 1 and 2; variational replica symmetry is monotone
-- statement:
--   Fix integers $d\ge3$ and $q\ge2$. Consider the hardcore model at $\alpha\in(0,1/2)$ or the antiferromagnetic Potts model at $\beta\in(0,1)$. If the parameter lies in the interior of the variational replica-symmetric regime (some $\alpha'\in(\alpha,1/2)$, resp. some $\beta'\in[0,\beta)$, has $\mathcal B_{d,\cdot}\le0$ on all of $\mathcal P_\pi$), then Condition 1 and Condition 2 hold at $(d,t)$. Moreover variational replica symmetry is monotone: for $0<\alpha<\alpha'<1/2$,
--   $$\big(\forall\nu\in\mathcal P_{\pi_{\alpha'}}:\ \mathcal B_{d,\alpha'}(\nu)\le0\big)\Longrightarrow\big(\forall\nu\in\mathcal P_{\pi_\alpha}:\ \mathcal B_{d,\alpha}(\nu)\le0\big),$$
--   and for Potts the same holds from $\beta'$ to $\beta$ whenever $0\le\beta'<\beta<1$.
--
--   It is how the definition (32) of $\alpha_{\mathrm{RSB}}$ feeds the strict conditions of Theorem 5.1.
--
--   Differences from the source:
--   - reading: 't lies in the interior of the variational replica-symmetric regime' → InteriorVariationalRS: hardcore ∃ α' ∈ (α, 1/2) with variational RS at α'; Potts ∃ β' ∈ [0, β) with variational RS at β'; reason: the regime is a down-set in α / up-set in β by the 'Moreover' clause; this is how the proof (p. 30) and §5.4 (p. 40, β' = 0) use the hypothesis
--   - reading: 'preserved under decreasing α for hardcore and increasing β for Potts' → hardcore: 0 < α < α' < 1/2; Potts: 0 ≤ β' < β < 1, variational RS at the first parameter implies it at the second; reason: the lemma's parameter ranges, with β' = 0 allowed as §5.4 applies it
--   - encoding: nonconstant eigenvalues κ_2(t), …, κ_|Ω|(t) of K_t counted with algebraic multiplicity → the set m.nonconstEig t of eigenvalues of K_t on {f : π(t)ᵀ f = 0}; reason: only max_a |κ_a| and the signs κ_a ≤ 0 are used; these depend only on the set of values
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 29, Lemma 4.17 (Conditions 1 and 2 on p. 29); the reading of 'interior' from the proof, p. 30, and §5.4, p. 40

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional

open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- **Lemma 4.17** (p. 29). Fix integers `d ≥ 3` and `q ≥ 2`. For the hardcore model at
`α ∈ (0, 1/2)` and for the antiferromagnetic Potts model at `β ∈ (0, 1)`: if the parameter lies in
the interior of the variational replica-symmetric regime, Conditions 1 and 2 hold at `(d, t)`.
Moreover variational replica symmetry is preserved under decreasing `α` (hardcore) and under
increasing `β` (Potts). -/
theorem lemma_4_17 (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ α : ℝ, 0 < α → α < 1 / 2 → InteriorVariationalRS .hardcore d α →
        Condition1 .hardcore d α ∧ Condition2 .hardcore d α) ∧
    (∀ β : ℝ, 0 < β → β < 1 → InteriorVariationalRS (.potts q) d β →
        Condition1 (.potts q) d β ∧ Condition2 (.potts q) d β) ∧
    (∀ α α' : ℝ, 0 < α → α < α' → α' < 1 / 2 →
        VariationalRS .hardcore d α' → VariationalRS .hardcore d α) ∧
    (∀ β' β : ℝ, 0 ≤ β' → β' < β → β < 1 →
        VariationalRS (.potts q) d β' → VariationalRS (.potts q) d β) := by sorry

end ZeroFreeRRG.Hardcore
