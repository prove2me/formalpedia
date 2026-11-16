-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_Supplement_general_inputs
-- name    : WitnessIsolation.AffineCollapse.Supplement.general_inputs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:53:32.861183+00:00
-- url     : https://prove2.me/theorems/2179b246-7017-4a68-9984-1453f989d4ee
-- title:
--   Theorem 1.3 — General inputs: harmonic-pool bound on SAT circuits
-- statement:
--   Let $I$ be a pruning transformation (polynomial resources, $\mathrm{Sol}(I(H;\rho))\subseteq\mathrm{Sol}(H)$ for every input and tape) with general witness-length guarantee $p$: for all sufficiently large $n$, on every satisfiable $n$-variable description of any length, $I$ outputs a uniquely satisfiable circuit with probability at least $p(n)$. Let $S(s,v)$ be the least size of a circuit deciding satisfiability of descriptions of length at most $s$ with at most $v$ variables, and $H_M=\sum_{k=1}^M1/k$. There are constants $D,E$, depending only on $I$ and the encoding, such that:
--
--   1. for all large $v$, all integers $M\ge2$, all $0<\Delta\le1$ with $p(v)\ge 1/H_M+\Delta$, and all $s\ge v$,
--   $$S(s,v)\le (s+M+\Delta^{-1})^D;$$
--   2. for all large $v$ with $p(v)>0$ and all $s\ge v$, $S(s,v)\le (s+2)^E\,2^{E/p(v)}$;
--   3. if $p(n)=g(n)/n$ with $g(n)\to\infty$, then for all large $v$ and $s\ge v$, $S(s,v)\le(s+2)^E\,2^{Ev/g(v)}$; and for every fixed polynomial cap $s\le c(v+2)^d$ and every $\eta>0$, $S(s,v)\le 2^{\eta v}$ for all large $v$, i.e. $S(s,v)=2^{o(v)}$.
--
--   The thresholds may depend on $p$; $D$ and $E$ do not. This is the paper's answer for isolators on all satisfiable inputs: any improvement of the Valiant–Vazirani success $\Omega(1/n)$ by a growing factor gives subexponential SAT circuits in the number of variables.
--
--   **Formalization Note** "$S(s,v)\le b$" is `SatBound`, which also asserts that $S(s,v)$ is finite. The $O(1)$ exponents are natural numbers $D,E$ chosen before $p$.
--
--   Differences from the source:
--   - encoding: S(s,v) ≤ b → SatBound s v b: S(s,v) is a finite N with N ≤ b; reason: S(s,v) is an ℕ∞ minimum; finiteness holds for every finite cap by the published exhaustive_search, so no instance changes
--   - encoding: constants D and O(1) depending only on I and the encoding; "for all large v" → natural D, E ≥ 1 quantified before p; an eventual threshold N quantified after p; reason: this is the stated dependency; the guarantee threshold enters only the threshold
--   - encoding: S(s,v) ≤ (s+2)^{O(1)} 2^{O(1/p(v))} → the bound (s+2)^E 2^{E/p(v)} under 0 < p(v); reason: for p(v) ≤ 0 the source bound is infinite or undefined, while Lean division by zero would return 0
--   - encoding: p(n) = g(n)/n → p(n) = g(n)/n for every n ≥ 1; reason: at n = 0 the source formula is undefined; Lean would force p(0) = 0
--   - encoding: 2^{o(v)} for s = poly(v) → for every c > 0, d ∈ ℕ and η > 0, eventually S(s,v) ≤ 2^{ηv} whenever v ≤ s ≤ c(v+2)^d; reason: the standard meaning of o(v), uniform over every fixed polynomial cap
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 2, PDF p. 3, Theorem 1.3; proof p. 9, PDF p. 10 (§4.1)

import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_success
import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_bounds
import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_harmonic

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- Theorem 1.3 (General inputs), printed p. 2 / PDF p. 3; proof printed p. 9 / PDF p. 10.
The exponents `D,E` depend only on `I` (and the fixed encoding) and precede the guarantee
`p` and all of `v,M,Δ,s`; the eventual thresholds may depend on `p`. -/
theorem general_inputs (I : PruningFamily) (hI : IsPruner I) :
    ∃ D E : ℕ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ p : ℕ → ℝ, GeneralGuarantee I p →
      (∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v →
        ∀ M : ℕ, 2 ≤ M → ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 →
        1 / (harmonic M : ℝ) + Δ ≤ p v → ∀ s : ℕ, v ≤ s →
          SatBound s v (((s:ℝ) + M + Δ⁻¹)^D)) ∧
      (∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v → ∀ s : ℕ, v ≤ s →
        (0 < p v → SatBound s v (((s:ℝ)+2)^E * (2:ℝ)^(E / p v)))) ∧
      (∀ g : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → p n = g n / (n:ℝ)) →
        Filter.Tendsto g Filter.atTop Filter.atTop →
        (∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v → ∀ s : ℕ, v ≤ s →
          SatBound s v (((s:ℝ)+2)^E * (2:ℝ)^((E:ℝ)*v/g v))) ∧
        (∀ c : ℝ, 0 < c → ∀ d : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v → ∀ s : ℕ, v ≤ s →
            PolynomialCap c d s v → SatBound s v ((2:ℝ)^(η*v)))) := by sorry

end WitnessIsolation.AffineCollapse.Supplement
