-- Prove2me | Theorems.Thm_mme_dwz_paired_exact_typical_useful_log_rate
-- name    : mme_dwz_paired_exact_typical_useful_log_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T14:58:20.414372+00:00
-- url     : https://prove2.me/theorems/64fc4f22-3912-4ea6-82ef-057cee7c0444
-- title:
--   Exact paired typical profiles retain the merged useful exponential rate
-- statement:
--   Let $S$ and $A$ be finite sets, let $\sigma:S\to S$ be an involutive bijection, and let $p_s:A\to\mathbb N$ be integer profiles with the same total $D$:
--   $$
--   \sigma(\sigma(s))=s,\qquad\sum_{a\in A}p_s(a)=D.
--   $$
--   Choose arbitrary integer weights $k_s\ge0$. For each integer $t\ge0$, define the exact paired-type count and the merged child-profile count by
--   $$
--   J(t)=\prod_{s\in S}
--   \binom{t k_sD^2}{\bigl(t k_s p_s(a)p_{\sigma(s)}(b)\bigr)_{(a,b)\in A^2}},
--   $$
--   $$
--   U(t)=\prod_{s\in S}
--   \binom{tD^2(k_s+k_{\sigma(s)})}{\bigl(tD(k_s+k_{\sigma(s)})p_s(a)\bigr)_{a\in A}}.
--   $$
--   Here each multinomial is its exact factorial quotient. Then, using natural logarithms,
--   $$
--   \lim_{t\to\infty}\frac{\log J(t)-\log U(t)}{t}=0.
--   $$
--   Consequently, for every $\varepsilon>0$, all sufficiently large $t$ satisfy
--   $$
--   J(t)\ge e^{-\varepsilon t}U(t).
--   $$
--   No equality $k_s=k_{\sigma(s)}$ is assumed. Zero profile entries, zero weights, zero common total, and empty finite sets are allowed; the corresponding multinomials remain positive. Thus exact independent paired profiles have no exponential counting loss relative to the merged useful profiles. Identifying these counts with a specific tensor's strongly useful and typical word subsets is a separate finite construction; this theorem does not assume or conclude a tensor restriction.
-- source:
--   Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5#A3, Appendix C, proof of Lemma 7.10, equations (41)–(44): independent paired profile counts and the strongly-useful/useful entropy comparison. Derived denominator-cleared generic analytic lemma, not a verbatim numbered theorem. Uses the public mme_scaled_multinomial_log_rate; complements mme_dwz_paired_product_type_card_and_marginals (295ef1dd-b822-4af6-9db2-35b57834928c).

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Fintype.Prod

open BigOperators Filter
open scoped Topology Classical
set_option autoImplicit false

theorem mme_dwz_paired_exact_typical_useful_log_rate
    {S A : Type*} [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (p : S → A → ℕ) (D : ℕ) (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ) :
    let J : ℕ → ℝ := fun t ↦ ∏ s, (Nat.multinomial Finset.univ
      (fun ab : A × A ↦ t * k s * p s ab.1 * p (sigma s) ab.2) : ℝ)
    let U : ℕ → ℝ := fun t ↦ ∏ s, (Nat.multinomial Finset.univ
      (fun a ↦ t * D * (k s + k (sigma s)) * p s a) : ℝ)
    Tendsto (fun t : ℕ ↦ (Real.log (J t) - Real.log (U t)) / (t : ℝ))
      atTop (𝓝 0) ∧
    ∀ eps : ℝ, 0 < eps → ∀ᶠ t : ℕ in atTop,
      Real.exp (-eps * (t : ℝ)) * U t ≤ J t := by sorry
