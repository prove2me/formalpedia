-- Prove2me | Theorems.Thm_Ziegler2002_zp_tucker
-- name    : Ziegler2002.zp_tucker
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T13:40:09.899974+00:00
-- url     : https://prove2.me/theorems/744936d5-530f-4668-b5e5-d5c550aac395
-- title:
--   Ziegler's Z_p-Tucker lemma (Pálvölgyi's Lemma 14 form) — an equivariant labelling of disjoint p-tuples with m ≤ ⌊(n−1)/(p−1)⌋ has a p-chain with one absolute value and all p signs
-- statement:
--   Let $p = q + 1$ be a prime and $n, m \ge 1$ with $m \le \lfloor (n-1)/(p-1) \rfloor$. Let $\lambda = (\lambda_1, \lambda_2)$ assign to every $p$-tuple $X = (X_0, \dots, X_{p-1})$ of subsets of $\{0, \dots, n-1\}$ a sign $\lambda_1(X) \in \mathbb Z_p$ (`Fin (q + 1)`, with addition mod $p$) and a value $\lambda_2(X) \in$ `Fin m`, and suppose $\lambda$ is equivariant on the tuples of pairwise disjoint, not all empty sets: for every such $X$, the cyclic shift $\sigma X = (X_{p-1}, X_0, \dots, X_{p-2})$ has
--   $$\lambda(\sigma X) = (\lambda_1(X) + 1, \lambda_2(X)).$$
--   Then there are $p$ such tuples $Y^{(0)} < Y^{(1)} < \dots < Y^{(p-1)}$, strictly increasing for coordinatewise inclusion, with all $\lambda_2(Y^{(j)})$ equal and the $p$ signs $\lambda_1(Y^{(j)})$ pairwise distinct (hence all of $\mathbb Z_p$).
--
--   Pálvölgyi, p. 13: “Let $\mathcal X_p(n)$ be the poset of tuples $X = (X_1, \dots, X_p)$ of pairwise disjoint subsets of $[n]$, not all empty, ordered by coordinatewise inclusion. Let $\sigma(X_1, \dots, X_p) = (X_p, X_1, \dots, X_{p-1})$. The group $\mathbb Z_p$ acts by powers of $\sigma$, and on $\mathbb Z_p \times [m]$ we use $\sigma(a, t) = (a + 1, t)$.” “Lemma 14 ($\mathbb Z_p$-Tucker lemma; Ziegler [53]). Let $p \ge 2$ be prime and let $n, m \ge 1$. If $\lambda : \mathcal X_p(n) \longrightarrow \mathbb Z_p \times [m]$ is equivariant and $m \le \left\lfloor \frac{n-1}{p-1} \right\rfloor$, then there is a strict chain $X^{(1)} < X^{(2)} < \cdots < X^{(p)}$ such that all $\lambda_2(X^{(j)})$ are equal and the $p$ signs $\lambda_1(X^{(j)})$ are the distinct elements of $\mathbb Z_p$.”
--
--   **External.** This is the case $s_1 = \dots = s_n = 1$ of Ziegler's Lemma 5.3 ([Invent. Math. 147 (2002) 671–691](https://doi.org/10.1007/s002220100188)), where a face of $(\sigma^{n-1})^{*p}_s$ with every $s_i = 1$ is exactly a $p$-tuple of pairwise disjoint subsets of $[n]$. For $p = 2$ it is Tucker's combinatorial lemma in its octahedral form. Pálvölgyi uses it to prove the Kneser–Tucker lemma (Lemma 15) and from that the Kneser-shift theorem [`Palvolgyi2026.kneser_shift`](https://prove2.me/theorems/88e50ee2-adbf-41ca-a769-564877b2c29d).
--
--   **Formalization note.** The prime is written $q + 1$, $\lfloor (n-1)/(p-1) \rfloor$ is natural-number division `(n - 1) / q`, $[m]$ is `Fin m`, and coordinates and signs are indexed by `Fin (q + 1)` from $0$. The labelling `lam` is given on all $p$-tuples of finite subsets of `Fin n`, but equivariance is assumed only on $\mathcal X_p(n)$, and the chain is required to lie in $\mathcal X_p(n)$; values off $\mathcal X_p(n)$ play no role. The strict chain is `StrictMono Y` for the coordinatewise order on tuples.
-- source:
--   Pálvölgyi, D., A nearcircumsphere-Ramsey theorem for solvable transitive configurations, arXiv:2608.10865v2 (2026), https://arxiv.org/abs/2608.10865, p. 13, Lemma 14 (the case s_1 = … = s_n = 1 of Ziegler, G. M., Generalized Kneser coloring theorems with combinatorial proofs, Invent. Math. 147 (2002) 671–691, https://doi.org/10.1007/s002220100188, Lemma 5.3)

import Mathlib

namespace Ziegler2002

theorem zp_tucker (q : ℕ) (hp : (q + 1).Prime) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmn : m ≤ (n - 1) / q)
    (lam : (Fin (q + 1) → Finset (Fin n)) → Fin (q + 1) × Fin m)
    (hlam : ∀ X : Fin (q + 1) → Finset (Fin n),
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) → (∃ i, (X i).Nonempty) →
        lam (fun i => X (i - 1)) = ((lam X).1 + 1, (lam X).2)) :
    ∃ Y : Fin (q + 1) → Fin (q + 1) → Finset (Fin n),
      (∀ j, (∀ i i', i ≠ i' → Disjoint (Y j i) (Y j i')) ∧ ∃ i, (Y j i).Nonempty) ∧
      StrictMono Y ∧ (∀ j j', (lam (Y j)).2 = (lam (Y j')).2) ∧
      Function.Injective (fun j => (lam (Y j)).1) := by
  sorry

end Ziegler2002
