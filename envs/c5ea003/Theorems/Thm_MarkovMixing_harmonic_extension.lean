-- Prove2me | Theorems.Thm_MarkovMixing_harmonic_extension
-- name    : MarkovMixing.harmonic_extension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:59:54.24982+00:00
-- url     : https://prove2.me/theorems/70114fe3-1f22-4348-8ea4-96d5484308bf
-- title:
--   Proposition 9.1 -- existence and uniqueness of harmonic extensions
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$. A function $h:V\to\mathbb R$ is **harmonic at** $x$ when it satisfies the mean-value property $h(x)=\sum_yP(x,y)\,h(y)$. Fix a nonempty set of states $B$ and boundary data $f:B\to\mathbb R$, write $\tau_B$ for the first time the chain visits $B$, and let $\mathbb P_x\{X_{\tau_B}=y\}$ denote the probability that the chain started at $x$ first enters $B$ at the state $y$. Define the **harmonic extension** of $f$ as its expected boundary value at the first visit,
--   $$h(x)=\mathbb E_x\bigl[f(X_{\tau_B})\bigr]=\sum_{y\in B}f(y)\,\mathbb P_x\{X_{\tau_B}=y\}.$$
--
--   The theorem (Proposition 9.1 of Levin–Peres–Wilmer) asserts:
--
--   1. $h$ agrees with $f$ on $B$;
--   2. $h$ is harmonic at every state outside $B$;
--   3. $h$ is the **unique** such function: any $g$ that agrees with $f$ on $B$ and is harmonic off $B$ equals $h$ everywhere.
--
--   This is the discrete Dirichlet problem: boundary data on $B$ extends in exactly one way to a function harmonic off $B$, and the extension is probabilistic. Voltages in the electrical dictionary are exactly such extensions.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 9.2, Proposition 9.1, p. 116

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Proposition 9.1** (LPW): for an irreducible chain and a nonempty set
`B` of states with boundary data `f`, the function
`h(x) = E_x f(X_{τ_B}) = ∑_{y ∈ B} f(y) P_x{X_{τ_B} = y}` is the unique
extension of `f` that agrees with `f` on `B` and is harmonic off `B`. -/
theorem harmonic_extension {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (B : Finset V) (hB : B.Nonempty) (f : V → ℝ) :
    (∀ x ∈ B, (∑ y ∈ B, f y * firstHitAtProb P x B y) = f x) ∧
    HarmonicOn P (fun x => ∑ y ∈ B, f y * firstHitAtProb P x B y)
      {x : V | x ∉ B} ∧
    ∀ g : V → ℝ, (∀ x ∈ B, g x = f x) → HarmonicOn P g {x : V | x ∉ B} →
      g = fun x => ∑ y ∈ B, f y * firstHitAtProb P x B y := by
  sorry

end MarkovMixing
