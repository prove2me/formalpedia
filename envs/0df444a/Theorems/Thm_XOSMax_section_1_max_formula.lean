-- Prove2me | Theorems.Thm_XOSMax_section_1_max_formula
-- name    : XOSMax.section_1_max_formula
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:24.386721+00:00
-- url     : https://prove2.me/theorems/b998aaa2-eb67-4be7-be20-65f3ac1525d7
-- title:
--   §1 display — $\max_X f(X)=\max_i\sum_v\max\{f_i(v),0\}$
-- statement:
--   Let $f$ be represented by clauses $f_1,\dots,f_k$ on a finite ground set $V$. Then
--   $$
--   \max_{X\subseteq V}f(X)=\max_{i\in[k]}\max_{X\subseteq V}f_i(X)=\max_{i\in[k]}\sum_{v\in V}\max\{f_i(v),0\}.
--   $$
--   More precisely:
--
--   1. for every $i$, the maximum of $f_i$ over the subsets of $V$ is $\sum_{v\in V}\max\{f_i(v),0\}$;
--   2. there is an index $p$ at which $\sum_{v\in V}\max\{f_i(v),0\}$ is largest, this value is the maximum of $f$ over the subsets of $V$, and the set $X^*=\{v\in V: f_p(v)>0\}$ attains it, with $f(X^*)=f_p(X^*)$.
--
--   This formula is why maximization is easy when the clauses are known, and the set $X^*$ is the optimum that the proofs of Lemmas 9 and 12 work with.
--
--   Differences from the source:
--   - encoding: equalities of maxima → `IsGreatest` statements with explicit witnesses; reason: the maxima are over finite nonempty families, and this form has no junk value
--   - generalization: the display only → the display plus the witness $X^*=\{v: f_p(v)>0\}$ with $f(X^*)=f_p(X^*)$; reason: the proofs of Lemmas 9 and 12 use this form, and dropping the extra conjuncts gives the display
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §1 display, p.1; the form with $X^*$: Lemma 9, proof, p.6, and Lemma 12, proof, p.8

import Mathlib
import Definitions.Def_XOSMax_Represents

namespace XOSMax

/-- The display of §1: `max_{X⊆V} f(X) = max_{i∈[k]} max_{X⊆V} fᵢ(X) = max_{i∈[k]} ∑_{v∈V} max{fᵢ(v), 0}`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, §1, p.1, "it is easy to maximize f").

**Formalization Note** The first clause is `max_{X⊆V} fᵢ(X) = ∑_{v∈V} max{fᵢ(v), 0}` for every `i`.
The second gives a clause `p` at which the maximum over `i` is attained, its value is
`max_{X⊆V} f(X)`, and `X* = { v ∈ V | f_p(v) > 0 }` attains it with `f(X*) = f_p(X*)`, the form used
in the proofs of Lemmas 9 and 12. -/
theorem section_1_max_formula {E : Type} [DecidableEq E] {k : ℕ} (V : Finset E)
    (w : Fin k → E → ℝ) (f : Finset E → ℝ) (hw : Represents w f) :
    (∀ i : Fin k, IsGreatest {s : ℝ | ∃ X ⊆ V, s = ∑ v ∈ X, w i v}
        (∑ v ∈ V, max (w i v) 0)) ∧
    ∃ p : Fin k,
      IsGreatest (Set.range fun i : Fin k => ∑ v ∈ V, max (w i v) 0)
        (∑ v ∈ V, max (w p v) 0) ∧
      IsGreatest {s : ℝ | ∃ X ⊆ V, s = f X} (∑ v ∈ V, max (w p v) 0) ∧
      f (V.filter fun v => 0 < w p v) = ∑ v ∈ V.filter (fun v => 0 < w p v), w p v ∧
      f (V.filter fun v => 0 < w p v) = ∑ v ∈ V, max (w p v) 0 := by sorry

end XOSMax
