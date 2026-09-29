-- Prove2me | solution 1 for BerggrenZeta.exists_node_of_prime_one_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:39:03.070999+00:00
-- url     : https://prove2.me/submissions/8cebf5ff-b21a-434e-855e-1de8f74bfafc

-- Sol generated from Novelty/BerggrenTreePrimeHypotenuse.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
import Definitions.Def_Novelty_BerggrenTreeZetaCore

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








open BerggrenZeta in
theorem solution{p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ w : List (Fin 3), hyp w = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  -- both `a` and `b` are positive
  have hp2 : 2 ≤ p := hp.two_le
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hb2 : b ^ 2 = p := by simpa using hab
    have hbd : b ∣ p := ⟨b, by rw [← hb2]; ring⟩
    rcases hp.eq_one_or_self_of_dvd b hbd with hb1 | hbp
    · rw [hb1] at hb2; simp at hb2; omega
    · rw [hbp] at hb2; nlinarith
  have hb0 : b ≠ 0 := by
    rintro rfl
    have ha2 : a ^ 2 = p := by simpa using hab
    have had : a ∣ p := ⟨a, by rw [← ha2]; ring⟩
    rcases hp.eq_one_or_self_of_dvd a had with ha1 | hap
    · rw [ha1] at ha2; simp at ha2; omega
    · rw [hap] at ha2; nlinarith
  -- they are coprime
  have hcop : Nat.Coprime a b := by
    by_contra hcon
    obtain ⟨q, hq, hqa, hqb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
    have hqp : q ∣ p := by
      rw [← hab]
      exact dvd_add (Dvd.dvd.pow hqa (by norm_num)) (Dvd.dvd.pow hqb (by norm_num))
    have hqeq : q = p := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp q hqp) with h | h
      · exact absurd h hq.one_lt.ne'
      · exact h
    subst hqeq
    have hqa' : q ≤ a := Nat.le_of_dvd (by omega) hqa
    have hqb' : q ≤ b := Nat.le_of_dvd (by omega) hqb
    nlinarith [hab, hq.two_le]
  -- opposite parity, since `p` is odd
  have hpar : (a + b) % 2 = 1 := by
    have hodd : p % 2 = 1 := by omega
    rcases Nat.even_or_odd a with ⟨x, hx⟩ | ⟨x, hx⟩ <;>
      rcases Nat.even_or_odd b with ⟨y, hy⟩ | ⟨y, hy⟩ <;>
      · have hax : a = _ := hx
        have hby : b = _ := hy
        subst hax; subst hby
        first
          | omega
          | (exfalso
             have : p = 4 * (x ^ 2 + y ^ 2) := by rw [← hab]; ring
             omega)
          | (exfalso
             have : p = 4 * (x ^ 2 + x + y ^ 2 + y) + 2 := by rw [← hab]; ring
             omega)
  have hne : a ≠ b := by
    intro h
    subst h
    omega
  -- order the pair into an admissible Euclid seed
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hseed : IsSeed (b, a) := ⟨hlt, by omega, (Nat.coprime_comm.mp hcop), by omega⟩
    obtain ⟨w, hw⟩ := isSeed_reachable _ hseed
    exact ⟨w, by simp only [hyp, hw]; omega⟩
  · have hseed : IsSeed (a, b) := ⟨hgt, by omega, hcop, hpar⟩
    obtain ⟨w, hw⟩ := isSeed_reachable _ hseed
    exact ⟨w, by simp only [hyp, hw]; omega⟩
