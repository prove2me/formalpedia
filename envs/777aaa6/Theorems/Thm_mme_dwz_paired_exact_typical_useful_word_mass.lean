-- Prove2me | Theorems.Thm_mme_dwz_paired_exact_typical_useful_word_mass
-- name    : mme_dwz_paired_exact_typical_useful_word_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T15:18:35.187191+00:00
-- url     : https://prove2.me/theorems/a99f861d-d6c7-4e4c-9526-a2b0658898c8
-- title:
--   Exact paired typical words form a nonempty subexponential fraction of merged useful words
-- statement:
--   Let $S$ and $A$ be finite sets, let $\sigma:S\to S$ be an involutive bijection, and let $p_s:A\to\mathbb N$ have common total $D$. Choose arbitrary weights $k_s\in\mathbb N$. For each $t\in\mathbb N$, let $P_t$ be a finite set of parent positions with an oriented cell map $c_t:P_t\to S$ satisfying
--   $$
--   |c_t^{-1}(s)|=t k_s D^2.
--   $$
--   The two child positions of $v\in P_t$ have cells $c_t(v)$ and $\sigma(c_t(v))$, respectively. A child word is a function $w:P_t\times\{0,1\}\to A$.
--
--   Define joint and merged counts by
--   $$
--   j_{t,s}(a,b)=t k_s p_s(a)p_{\sigma(s)}(b),\qquad
--   u_{t,s}(a)=tD(k_s+k_{\sigma(s)})p_s(a).
--   $$
--   Let $\mathcal U_t$ consist of the child words having exactly $u_{t,s}(a)$ occurrences of symbol $a$ in child cell $s$. Let $\mathcal T_t\subseteq\mathcal U_t$ consist of those words whose paired symbols $(w(v,0),w(v,1))$ have exactly $j_{t,s}(a,b)$ occurrences in parent cell $s$.
--
--   Then $\mathcal T_t$ is nonempty for every $t$, and both actual word counts are exact:
--   $$
--   |\mathcal T_t|=\prod_{s\in S}\binom{t k_sD^2}{(j_{t,s}(a,b))_{(a,b)\in A^2}},\qquad
--   |\mathcal U_t|=\prod_{s\in S}\binom{tD^2(k_s+k_{\sigma(s)})}{(u_{t,s}(a))_{a\in A}}.
--   $$
--   Moreover, for any tag set $B$, any map $\tau:S\times A^2\to B$, any $z\in B$, and any $w\in\mathcal T_t$,
--   $$
--   \bigl|\{v\in P_t:\tau(c_t(v),w(v,0),w(v,1))=z\}\bigr|
--   =\sum_{s\in S}\sum_{a,b\in A}[\tau(s,a,b)=z]j_{t,s}(a,b).
--   $$
--   For every $\varepsilon>0$, all sufficiently large $t$ satisfy
--   $$
--   |\mathcal T_t|\ge e^{-\varepsilon t}|\mathcal U_t|.
--   $$
--   Here the multinomials are exact natural-number factorial quotients. Zero entries, zero weights, $D=0$, and empty finite alphabets are included; no symmetry of the weights is assumed. This is a concrete subset and counting result for paired words. Applying it to particular DWZ quarter-word tags and proving a tensor restriction or a positive-component value remain separate tasks.
-- source:
--   Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5#A3, Appendix C, proof of Lemma 7.10, equations (41)–(44). Derived generic finite-word and counting formulation of independent paired profiles. Uses the proved mme_dwz_paired_product_type_card_and_marginals, mme_prescribed_cell_histogram_card, and mme_dwz_paired_exact_typical_useful_log_rate.

import Definitions.Def_mme_recursive_yz_compatibility
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Fintype.Prod

open BigOperators Filter MME.RecursiveYZ
open scoped Classical Topology
set_option autoImplicit false

theorem mme_dwz_paired_exact_typical_useful_word_mass
    {S A Tag : Type*} [Fintype S] [Fintype A]
    (sigma : S ≃ S) (hsigma : ∀ s, sigma (sigma s) = s)
    (p : S → A → ℕ) (D : ℕ) (hp : ∀ s, ∑ a, p s a = D) (k : S → ℕ)
    (P : ℕ → Type*) [∀ t, Fintype (P t)] (cell : ∀ t, P t → S)
    (hsize : ∀ t s, Fintype.card {v : P t // cell t v = s} = t * k s * D * D) :
    let child : ∀ t, P t × Fin 2 → S := fun t v ↦
      if v.2 = 0 then cell t v.1 else sigma (cell t v.1)
    let joint : ℕ → S → A × A → ℕ := fun t s ab ↦
      t * k s * p s ab.1 * p (sigma s) ab.2
    let merged : ℕ → S → A → ℕ := fun t s a ↦
      t * D * (k s + k (sigma s)) * p s a
    let typical : ∀ t, (P t × Fin 2 → A) → Prop := fun t w ↦
      Useful (child t) (merged t) w ∧
      Useful (cell t) (joint t) (fun v ↦ (w (v, 0), w (v, 1)))
    (∀ t,
      (∃ w : P t × Fin 2 → A, typical t w) ∧
      Fintype.card {w : P t × Fin 2 → A // typical t w} =
        ∏ s, Nat.multinomial Finset.univ (joint t s) ∧
      Fintype.card {w : P t × Fin 2 → A // Useful (child t) (merged t) w} =
        ∏ s, Nat.multinomial Finset.univ (merged t s) ∧
      ∀ w : P t × Fin 2 → A, typical t w →
        ∀ (tag : S → A × A → Tag) (z : Tag),
          Fintype.card {v : P t // tag (cell t v) (w (v, 0), w (v, 1)) = z} =
            ∑ s, ∑ ab : A × A, if tag s ab = z then joint t s ab else 0) ∧
    ∀ eps : ℝ, 0 < eps → ∀ᶠ t : ℕ in atTop,
      Real.exp (-eps * (t : ℝ)) *
        (Fintype.card {w : P t × Fin 2 → A // Useful (child t) (merged t) w} : ℝ) ≤
      (Fintype.card {w : P t × Fin 2 → A // typical t w} : ℝ) := by sorry
