-- Prove2me | Theorems.Thm_MarkovMixing_spectral_representation
-- name    : MarkovMixing.spectral_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:45:47.250824+00:00
-- url     : https://prove2.me/theorems/4ff47e98-f4f7-4228-ba00-1a9d39e87beb
-- title:
--   Lemma 12.2 -- the spectral representation of a reversible chain
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ with $n=|V|$ states, reversible with respect to a strictly positive probability distribution $\pi$ — that is, satisfying the detailed balance equations $\pi(x)P(x,y)=\pi(y)P(y,x)$. Equip real-valued functions on $V$ with the weighted inner product
--   $$\langle f,g\rangle_\pi=\sum_{x\in V}f(x)\,g(x)\,\pi(x),$$
--   the geometry in which a reversible chain is self-adjoint.
--
--   The theorem (Lemma 12.2 of Levin–Peres–Wilmer) asserts the existence of real numbers $\lambda_1,\dots,\lambda_n$ and functions $f_1,\dots,f_n:V\to\mathbb R$ such that:
--
--   1. each $f_j$ is an eigenfunction, $Pf_j=\lambda_jf_j$ (with $(Pf)(x)=\sum_yP(x,y)f(y)$);
--   2. the family is **orthonormal** in $\ell^2(\pi)$: $\langle f_j,f_k\rangle_\pi=1$ if $j=k$ and $0$ otherwise;
--   3. the transition probabilities decompose spectrally: for every time $t$ and all states $x,y$,
--   $$\frac{P^t(x,y)}{\pi(y)}=\sum_{j=1}^{n}f_j(x)\,f_j(y)\,\lambda_j^{\,t}.$$
--
--   Every question about the long-run behaviour of a reversible chain thereby becomes a question about the decay of the powers $\lambda_j^t$ — the formula from which the relaxation-time bounds of this mission and the cutoff theory of later missions are read off.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 12.1, Lemma 12.2, pp. 153-154

import Definitions.Def_mm_spectral

namespace MarkovMixing

/-- **Lemma 12.2** (LPW): a chain reversible with respect to a positive
distribution `π` admits an orthonormal basis of `ℓ²(π)` consisting of real
eigenfunctions, and the transition probabilities decompose spectrally:
`P^t(x,y)/π(y) = ∑_j f_j(x) f_j(y) λ_j^t`. -/
theorem spectral_representation {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x)
    (hrev : DetailedBalance P π) :
    ∃ (lam : Fin (Fintype.card V) → ℝ) (f : Fin (Fintype.card V) → V → ℝ),
      (∀ j, P.mulVec (f j) = lam j • f j) ∧
      (∀ j k, innerPi π (f j) (f k) = if j = k then 1 else 0) ∧
      ∀ (t : ℕ) (x y : V),
        (P ^ t) x y / π y = ∑ j, f j x * f j y * lam j ^ t := by
  sorry

end MarkovMixing
