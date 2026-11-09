-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_sat_checker_transfer
-- name    : WitnessIsolation.AffineCollapse.sat_checker_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:32:44.51537+00:00
-- url     : https://prove2.me/theorems/62da44ad-128d-4ccf-8181-59fad2472340
-- title:
--   Theorem 5.3 — Transfer with a SAT-based checker
-- statement:
--   Fix a polynomial-resource pruning transformation I. There are fixed polynomial bounds P,Q such that, whenever p is a witness-length guarantee from n₀, 1≤v≤ℓ, t≥2, tv≥n₀, 0<Δ≤1 and
--
--   $$p(tv)\ge\frac2{t+1}+\Delta,$$
--
--   some deterministic circuit separates uniquely satisfiable from unsatisfiable descriptions of actual length at most ℓ and with at most v declared variables. Its size is at most
--
--   $$P(\ell+v+t+\Delta^{-1}+2)\,[1+S(Q(\ell+v+t+2),t)].$$
--
--   Both polynomial choices precede p, n₀, ℓ,v,t,Δ and every smaller SAT circuit; they depend only on I and the fixed encoding. This is a separator existence claim with a linear smaller-SAT cost, and imposes no behavior on multi-solution inputs.
--
--   **Formalization Note** P and Q are represented by dominating monomials with natural coefficients and exponents. The inverse gap is rounded upward before the monomial is evaluated. No explicit constant from the paper is changed.
--
--   Differences from the source:
--   - encoding: fixed polynomial bounds on real argument ℓ+v+t+Δ⁻¹+2 and integer query cap → uniform natural monomials, with ceil(Δ⁻¹) in the first argument and extended-natural SAT minimum; reason: Δ>0 and Δ≤1 give equivalent polynomial bounds after absorbing a fixed coefficient; Equation (2.2) asserts finite attainment of S
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Theorem 5.3, printed pp. 10–11, PDF pp. 11–12; conclusion continues onto PDF p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Theorem 5.3. The length polynomial is chosen before all smaller SAT circuits. -/
theorem sat_checker_transfer (I : PruningFamily) (hI : IsPruner I) :
    ∃ c k d e : ℕ, 1 ≤ c ∧ 1 ≤ d ∧
      ∀ (p : ℕ → ℝ) (n₀ : ℕ), GuaranteeFrom I p n₀ →
      ∀ ℓ v t : ℕ, 1 ≤ v → v ≤ ℓ → 2 ≤ t → n₀ ≤ t*v →
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 → 2/((t:ℝ)+1)+Δ ≤ p (t*v) →
      ∃ C : Circuit (paddedWidth ℓ) 1, SeparatesUnique ℓ v C ∧
        (C.size : ℕ∞) ≤ (c*(ℓ+v+t+Nat.ceil Δ⁻¹+2)^k : ℕ) *
          (1 + satComplexity (d*(ℓ+v+t+2)^e) t) := by sorry

end WitnessIsolation.AffineCollapse
