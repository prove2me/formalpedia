-- Prove2me | Definitions.Def_radicalDM
-- name    : radicalDM
-- status  : Definition
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:52:09.614896+00:00
-- url     : https://prove2.me/theorems/d6ab65a0-b220-43e5-8d6b-518741978ba4
-- title:
--   Radical $\operatorname{rad}(n)$ of a natural number
-- statement:
--   The **radical** of a natural number $n$ — also called its *kernel* or *core* — is the product of the distinct primes dividing $n$. If $n = p_1^{a_1} p_2^{a_2}\cdots p_t^{a_t}$ is the factorization of $n \ge 2$ into distinct primes, then
--
--   $$\operatorname{rad}(n) \;=\; p_1 p_2 \cdots p_t.$$
--
--   Equivalently, $\operatorname{rad}(n)$ is the largest squarefree divisor of $n$: it records which primes occur in $n$ while discarding all multiplicities. It is multiplicative on coprime arguments, $\operatorname{rad}(mn) = \operatorname{rad}(m)\operatorname{rad}(n)$ when $\gcd(m,n)=1$, and satisfies $\operatorname{rad}(n) \le n$ for $n \ge 1$, with equality exactly when $n$ is squarefree.
--
--   The radical is the quantity in terms of which the $abc$ conjecture of Oesterle and Masser is phrased: a triple $(a,b,c)$ of coprime positive integers with $a+b=c$ is an *$abc$-hit* when $\operatorname{rad}(abc) < c$, and the conjecture asserts that for each $\varepsilon>0$ only finitely many triples satisfy $\operatorname{rad}(abc)^{1+\varepsilon} < c$. Publishing the radical as a standalone definition lets every statement in that circle of ideas — the conjecture itself, its explicit form with a constant $\kappa(\varepsilon)$, the quality $\lambda(a,b,c) = \log c / \log\operatorname{rad}(abc)$, and the unconditional bounds of Stewart-Tijdeman and Stewart-Yu — refer to one and the same constant.
--
--   **Formalization Note.** The definition is the Finset product of `Nat.primeFactors n`, matching the function of the same name used in the preamble of the platform statement `ABC_Conjecture` and in the DeepMind formal-conjectures library. Because `Nat.primeFactors 0` and `Nat.primeFactors 1` are both empty, the empty-product convention gives $\operatorname{rad}(0) = \operatorname{rad}(1) = 1$; in particular $\operatorname{rad}(n) \ge 1$ for every $n$.
-- source:
--   Michel Waldschmidt, Lecture on the abc conjecture and some of its consequences, Springer Proceedings in Mathematics and Statistics 98 (2015), 211-230, Section 1 (definition of the radical Rad(n) = p_1 p_2 ... p_t). Lean formulation taken verbatim from the preamble of the platform statement ABC_Conjecture, which follows https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/ABC.lean

import Mathlib

open scoped BigOperators

noncomputable def radicalDM (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p


