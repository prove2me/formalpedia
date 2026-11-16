-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_Supplement_graded_consequences
-- name    : WitnessIsolation.AffineCollapse.Supplement.graded_consequences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:55:28.417223+00:00
-- url     : https://prove2.me/theorems/ca6b12d4-0720-4fce-9a50-8ddf278e9ded
-- title:
--   Theorem 1.5 — Graded consequences of affine guarantees below inverse-polylogarithmic success
-- statement:
--   Let $I$ be a pruning transformation with (affine) witness-length guarantee $p$, and let $S(s,v)$ be the SAT circuit complexity, with logarithms base two.
--
--   1. If $p(n)\ge 2^{-C(\log(n+2))^{\epsilon}}$ for fixed $C>0$ and $0<\epsilon<1$, then
--   $$S(s,v)\le (s+2)^{(\log\log(v+4))^{O(1)}}\quad(s\ge v),$$
--   and every language in NP has circuits of size $m^{(\log\log m)^{O(1)}}$ at input length $m$.
--   2. If $p(n)\ge c\,n^{-\delta}$ for fixed $c>0$ and $0<\delta<1/2$, then $S(s,v)\le(s+2)^{(\log(v+2))^{O(1)}}$ for $s\ge v$, and every language in NP has quasipolynomial-size circuits.
--   3. If $p(n)\ge C/\sqrt n$ for a fixed $C>2$, then there is a constant $\alpha$ with $0<\alpha<1$ such that
--   $$S(s,v)\le 2^{O(v^\alpha(\log(v+2))^{1-\alpha})}\quad\text{whenever } v\le s\le\mathrm{poly}(v).$$
--   4. If $p(n)=\omega(n^{-1/2})$, i.e. $\sqrt n\,p(n)\to\infty$, then $S(s,v)\le(s+2)^{v^{o(1)}}$ for $s\ge v$, and for $s=\mathrm{poly}(v)$ this is $2^{v^{o(1)}}$.
--
--   In 1–3 the hidden constants depend only on $I$ and the fixed premise parameters (for the language clauses also on the language), not on $s$, $v$ or the particular $p$; in 3, $\alpha$ depends only on $I$ and $C$ and the $O$-constant also on the polynomial cap. All bounds hold for all sufficiently large $v$ (respectively $m$).
--
--   These are the circuit upper bounds that the recurrence still yields between the inverse-polylogarithmic range of Theorem 1.1 and success of order $n^{-1/2}$.
--
--   **Formalization Note** $(\log\log(v+4))^{O(1)}$ is $K(\log\log(v+4))^k$ with $K>0$, $k\in\mathbb N$; quasipolynomial size is $m^{K'(\log m)^{k'}}$; "$\mathrm{poly}(v)$" is every cap $s\le c(v+2)^d$; $v^{o(1)}$ is "for every $\eta>0$, eventually at most $v^\eta$", with thresholds independent of $s$. Language bounds are actual circuits in the published model (`LanguageBound`).
--
--   Differences from the source:
--   - generalization: premise p(n) ≥ f(n) → p(n) ≥ f(n) for all sufficiently large n; reason: a weaker hypothesis; the guarantee is itself eventual, and for p ≥ f everywhere this is the source claim
--   - encoding: exponents (log log(v+4))^{O(1)}, (log(v+2))^{O(1)}, m^{(log log m)^{O(1)}} and quasipolynomial size → K·(log log(v+4))^k, K·(log(v+2))^k, m^{K′(log log m)^{k′}} and m^{K′(log m)^{k′}} with K, K′ > 0 real and k, k′ natural, quantified before p; reason: for large arguments a constant factor is absorbed by one more power, so these are the same classes of bounds
--   - encoding: every language in NP has circuits of the stated size at input length m → for every L with the published InNP, actual circuits of the stated size at every sufficiently large m (LanguageBound), constants depending on L but not on p; reason: small input lengths are finitely many and do not affect an asymptotic size bound
--   - encoding: a constant α < 1 and 2^{O(…)} whenever v ≤ s ≤ poly(v) → 0 < α < 1 chosen before the cap and p; for every c > 0 and d a constant K, eventually S(s,v) ≤ 2^{K v^α (log(v+2))^{1−α}} when v ≤ s ≤ c(v+2)^d; reason: the bound grows with α once v ≥ log(v+2), so requiring α > 0 loses nothing
--   - encoding: p(n) = ω(n^{−1/2}); exponents v^{o(1)} → √n·p(n) → ∞; for every η > 0, eventually S(s,v) ≤ (s+2)^{v^η} for all s ≥ v, and S(s,v) ≤ 2^{v^η} under every polynomial cap; reason: standard meanings of ω and o(1); thresholds are independent of s
--   - encoding: S(s,v) ≤ b → SatBound s v b (S(s,v) finite and at most b); reason: S(s,v) is an ℕ∞ minimum; see the published exhaustive_search
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 3, PDF p. 4, Theorem 1.5 (i)–(iv); proofs pp. 14–15, PDF pp. 15–16 (§§7.2–7.5)

import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_bounds

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- Theorem 1.5 (Graded consequences), printed p. 3 / PDF p. 4; proofs printed pp. 14–15 /
PDF pp. 15–16: the conjunction of parts (i)–(iv). In (i)–(iii) the constants precede the
guarantee `p` and depend only on `I` and the fixed premise parameters (and, for the
language clauses, on the language); thresholds may depend on `p`. -/
theorem graded_consequences (I : PruningFamily) (hI : IsPruner I) :
    -- (i)
    (∀ C ε : ℝ, 0 < C → 0 < ε → ε < 1 →
      ∃ K : ℝ, 0 < K ∧ ∃ k : ℕ,
        (∀ p : ℕ → ℝ, HasGuarantee I p →
          (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            (2:ℝ)^(-C * (Real.logb 2 ((n:ℝ)+2))^ε) ≤ p n) →
          ∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v → ∀ s : ℕ, v ≤ s →
            SatBound s v (((s:ℝ)+2)^(K*(Real.logb 2 (Real.logb 2 ((v:ℝ)+4)))^k))) ∧
        (∀ L : Set (List Bool), InNP L → ∃ K' : ℝ, 0 < K' ∧ ∃ k' : ℕ,
          ∀ p : ℕ → ℝ, HasGuarantee I p →
          (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            (2:ℝ)^(-C * (Real.logb 2 ((n:ℝ)+2))^ε) ≤ p n) →
          LanguageBound L (fun m => (m:ℝ)^
            (K'*(Real.logb 2 (Real.logb 2 (m:ℝ)))^k')))) ∧
    -- (ii)
    (∀ c δ : ℝ, 0 < c → 0 < δ → δ < 1/2 →
      ∃ K : ℝ, 0 < K ∧ ∃ k : ℕ,
        (∀ p : ℕ → ℝ, HasGuarantee I p →
          (∃ N : ℕ, ∀ n : ℕ, N ≤ n → c*(n:ℝ)^(-δ) ≤ p n) →
          ∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v → ∀ s : ℕ, v ≤ s →
            SatBound s v (((s:ℝ)+2)^(K*(Real.logb 2 ((v:ℝ)+2))^k))) ∧
        (∀ L : Set (List Bool), InNP L → ∃ K' : ℝ, 0 < K' ∧ ∃ k' : ℕ,
          ∀ p : ℕ → ℝ, HasGuarantee I p →
          (∃ N : ℕ, ∀ n : ℕ, N ≤ n → c*(n:ℝ)^(-δ) ≤ p n) →
          LanguageBound L (fun m => (m:ℝ)^(K'*(Real.logb 2 (m:ℝ))^k')))) ∧
    -- (iii)
    (∀ C : ℝ, 2 < C → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ c : ℝ, 0 < c → ∀ d : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ p : ℕ → ℝ, HasGuarantee I p →
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → C/Real.sqrt (n:ℝ) ≤ p n) →
      ∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v → ∀ s : ℕ, v ≤ s →
        PolynomialCap c d s v →
          SatBound s v ((2:ℝ)^(K*(v:ℝ)^α *
            (Real.logb 2 ((v:ℝ)+2))^(1-α)))) ∧
    -- (iv)
    (∀ p : ℕ → ℝ, HasGuarantee I p →
      Filter.Tendsto (fun n : ℕ => Real.sqrt (n:ℝ) * p n) Filter.atTop Filter.atTop →
      (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v →
        ∀ s : ℕ, v ≤ s → SatBound s v (((s:ℝ)+2)^((v:ℝ)^η))) ∧
      (∀ c : ℝ, 0 < c → ∀ d : ℕ, ∀ η : ℝ, 0 < η →
        ∃ N : ℕ, ∀ v : ℕ, N ≤ v → 1 ≤ v → ∀ s : ℕ, v ≤ s →
          PolynomialCap c d s v → SatBound s v ((2:ℝ)^((v:ℝ)^η)))) := by sorry

end WitnessIsolation.AffineCollapse.Supplement
