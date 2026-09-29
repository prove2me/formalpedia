-- Prove2me | solution 1 for BerggrenZeta.primeNode_zeta_ge_primeSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:47:54.04111+00:00
-- url     : https://prove2.me/submissions/37cc47b3-e191-4fd1-9fce-684b09577025

-- Sol generated from Novelty/BerggrenTreePrimeHypotenuse.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
import Definitions.Def_Novelty_BerggrenTreeZetaCore
import Theorems.Thm_BerggrenZeta_exists_node_of_prime_one_mod_four
import Theorems.Thm_BerggrenZeta_hyp_mod_four
import Theorems.Thm_BerggrenZeta_treeZeta_summable_iff

/-!
# Prime hypotenuses in the Berggren tree

Which primes occur as hypotenuses of nodes of the Berggren tree?  Since the nodes are
exactly the Euclid seeds (`seedEquiv`) and `c = m² + n²` with `m + n` odd and
`gcd (m,n) = 1`, the answer is governed by Fermat's two-square theorem:

* `hyp_mod_four` — **every** hypotenuse in the tree is `≡ 1 (mod 4)`;
* `prime_hyp_iff` — a prime is the hypotenuse of some node **iff** it is `≡ 1 (mod 4)`;
* `infinite_prime_hyp` — hence, by Dirichlet's theorem, infinitely many nodes of the tree
  carry a prime hypotenuse;
* `summable_primeNode_zeta` — the prime-node Dirichlet series `∑_{c(w) prime} c(w)^{-s}`
  converges for `s > 1`, and
* `primeNode_zeta_ge_primeSum` — it dominates the `χ₄`-restricted prime zeta function
  `∑_{p ≡ 1 (4)} p^{-s}`.

Consequently the "prime number theorem for the Berggren tree" is *not* a new analytic
phenomenon: the prime-hypotenuse counting function of the tree is the counting function of
the primes in the arithmetic progression `1 mod 4`, so an error term of square-root quality
for it is precisely the classical Riemann Hypothesis for the Dirichlet `L`-function
`L(s, χ₄)`.  The Berggren tree therefore transports, but does not simplify, the prime
distribution problem; what it *does* possess unconditionally is the silver critical line of
`Novelty.BerggrenTreeCriticalLine`.
-/

open BerggrenZeta



/-- **The prime hypotenuses of the Berggren tree are exactly the primes `≡ 1 mod 4`.** -/
theorem prime_hyp_iff {p : ℕ} (hp : p.Prime) :
    (∃ w : List (Fin 3), hyp w = p) ↔ p % 4 = 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact hyp_mod_four w
  · exact exists_node_of_prime_one_mod_four hp


/-- The prime-node Dirichlet series `∑_{c(w) prime} c(w)^{-s}` converges for `s > 1`, being
dominated termwise by the full tree zeta series. -/
theorem summable_primeNode_zeta {s : ℝ} (hs : 1 < s) :
    Summable (fun w : List (Fin 3) =>
      if (hyp w).Prime then (hyp w : ℝ) ^ (-s) else 0) := by
  refine Summable.of_nonneg_of_le (fun w => ?_) (fun w => ?_)
    ((treeZeta_summable_iff s).mpr hs)
  · split
    · positivity
    · exact le_rfl
  · split
    · exact le_rfl
    · positivity



open BerggrenZeta in
theorem solution{s : ℝ} (hs : 1 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 1) :
    ∑ p ∈ P, (p : ℝ) ^ (-s) ≤
      ∑' w : List (Fin 3), (if (hyp w).Prime then (hyp w : ℝ) ^ (-s) else 0) := by
  classical
  -- pick a node for each prime of `P`
  have hchoice : ∀ p ∈ P, ∃ w : List (Fin 3), hyp w = p := by
    intro p hp
    obtain ⟨hp1, hp4⟩ := hP p hp
    exact (prime_hyp_iff hp1).mpr hp4
  choose! node hnode using hchoice
  have hinj : Set.InjOn node P := by
    intro p hp q hq hpq
    have h1 := hnode p hp
    have h2 := hnode q hq
    rw [hpq] at h1
    omega
  have himg : ∑ p ∈ P, (p : ℝ) ^ (-s)
      = ∑ w ∈ P.image node, (if (hyp w).Prime then (hyp w : ℝ) ^ (-s) else 0) := by
    rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨hp1, -⟩ := hP p hp
    rw [hnode p hp, if_pos hp1]
  rw [himg]
  refine (summable_primeNode_zeta hs).sum_le_tsum _ (fun w _ => ?_)
  split
  · positivity
  · exact le_rfl
