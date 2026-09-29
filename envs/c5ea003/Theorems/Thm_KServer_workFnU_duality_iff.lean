-- Prove2me | Theorems.Thm_KServer_workFnU_duality_iff
-- name    : KServer.workFnU_duality_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T19:46:01.491794+00:00
-- url     : https://prove2.me/theorems/c778beb1-ae44-4850-8e46-10ff5dadae46
-- title:
--   The duality lemma as an equivalence
-- statement:
--   Let $w$ be a work function, $r$ a point, and $w' = w \wedge r$ the work function after $r$ is requested. Then a configuration $A$ is a **minimizer of $w$ with respect to $r$** — that is,
--   $$A \in \arg\min_X\ \bigl(w(X) - d(r^k, X)\bigr)$$
--   — **if and only if** both of the following hold:
--
--   $$A \in \arg\max_X\ \bigl(w'(X) - w(X)\bigr) \qquad\text{and}\qquad A \in \arg\min_X\ \bigl(w'(X) - d(r^k, X)\bigr).$$
--
--   ## Role
--
--   The forward implication is the duality lemma of Koutsoupias and Papadimitriou, and it is what makes the pseudocost method work: it says that the configuration realising the extended cost of a request can be taken to be a minimizer, and that being a minimizer is preserved by the update. The converse is the observation of Coester and Koutsoupias that the implication is in fact an equivalence, so that "minimizer with respect to $r$" is characterised by the two conditions after the request rather than merely implying them.
--
--   The converse costs one line. The first condition, written out, is
--   $$w'(A) + w(B) \;\ge\; w(A) + w'(B),$$
--   and the second is
--   $$w'(B) - d(r^k,B) \;\ge\; w'(A) - d(r^k,A);$$
--   adding them, the terms in $w'$ cancel and what is left is exactly
--   $w(B) - d(r^k,B) \ge w(A) - d(r^k,A)$.
--
--   Worth noting, as the authors do, that no use is made of the triangle inequality: the argument is about the ordering of the four quantities alone.
--
--   **Formalization note.** The distance $d(r^k, X)$ from the configuration with all $k$ servers at $r$ is the sum $\sum_i d(r, X_i)$, since every server must reach $r$. The work function here is the unified one, which minimises over relabellings of the target configuration and so depends only on the multiset of occupied points.
-- source:
--   C. Coester, E. Koutsoupias, Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle, ICALP 2021, arXiv:2102.10474, Section 2 (Duality lemma): 'We give a slightly stronger version of the duality lemma by stating it as an equivalence rather than an implication.' The forward direction is E. Koutsoupias and C. Papadimitriou, On the k-server conjecture, JACM 42(5) (1995) 971-983.

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_duality_iff (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M) :
    (∀ X : Config k M,
        workFnU C₀ σ A - ∑ i, dist r (A i) ≤ workFnU C₀ σ X - ∑ i, dist r (X i))
      ↔ ((∀ X : Config k M,
            workFnU C₀ (σ ++ [r]) A - ∑ i, dist r (A i)
              ≤ workFnU C₀ (σ ++ [r]) X - ∑ i, dist r (X i))
          ∧ (∀ X : Config k M,
            workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
              ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A)) := by sorry

end KServer
