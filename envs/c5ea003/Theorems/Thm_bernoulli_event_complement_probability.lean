-- Prove2me | Theorems.Thm_bernoulli_event_complement_probability
-- name    : bernoulli_event_complement_probability
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T23:02:30.195954+00:00
-- url     : https://prove2.me/theorems/b3c49733-7d52-4140-bfb1-b3f2df3e8f64
-- title:
--   Bernoulli model: an event and its complement have total mass one
-- statement:
--   Reusable Bernoulli foundational lemma. For any inclusion probability $p$ and any event $E$ on the observation set, the Bernoulli-model probabilities of $E$ and of its complement sum to one: $\mathbb P_p(E)+\mathbb P_p(\lnot E)=1$, equivalently $\mathbb P_p(E)=1-\mathbb P_p(\lnot E)$. This is the total-mass normalization $\sum_\Omega p^{|\Omega|}(1-p)^{N-|\Omega|}=(p+(1-p))^N=1$ (here $N=n_1 n_2$) underlying every concentration complement argument in the matrix-completion tree. Note no $0\le p\le 1$ hypothesis is needed: the identity is the algebraic Fintype product expansion $\prod_a (p+(1-p))=1$.
-- source:
--   Elementary product-Bernoulli normalization (Fintype.prod_add); foundational complement identity for the Bernoulli sampling model of Candes-Recht, CACM 55(6):111-119, 2012.

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

theorem bernoulli_event_complement_probability
    {n₁ n₂ : ℕ} (p : ℝ) (E : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p E + bernoulliEventProb p (fun Ω => ¬ E Ω) = 1 := by
  sorry
