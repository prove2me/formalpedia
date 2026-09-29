-- Prove2me | Theorems.Thm_mme_dwz_joint_hash_ambient_xy_isolation_nonhole_mass
-- name    : mme_dwz_joint_hash_ambient_xy_isolation_nonhole_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:07:48.508644+00:00
-- url     : https://prove2.me/theorems/47b9af28-cc5c-4ebe-995e-5a90dec835b0
-- title:
--   A single asymmetric hash state retains substantial nonhole mass
-- statement:
--   Let $\Omega\ne\varnothing$ be a finite set of hash states, $U$ a finite address universe, and $\mathcal B$ a finite block set. Fix target and ambient sets $T,A\subseteq U$, address maps $x,y$, and retention events $E(a)\subseteq\Omega$.
--
--   Let $K,J,p,d,c$ be nonnegative integers with
--   $$
--   K=pJ,\qquad 4d\le p,\qquad 8c\le p.
--   $$
--   Assume that, for every $a\in T$:
--
--   - $|E(a)|=K$;
--   - each of $\{b\in A:x(b)=x(a)\}$ and $\{b\in A:y(b)=y(a)\}$ has size at most $d$;
--   - if $b\in A$, $b\ne a$, and $x(b)=x(a)$ or $y(b)=y(a)$, then $|E(a)\cap E(b)|\le J$;
--   - for each $z\in\mathcal B$, a competitor set $C(a,z)\subseteq U$ has size at most $c$, and $|E(a)\cap E(b)|\le J$ for every $b\in C(a,z)$.
--
--   For $w\in\Omega$, let $M(w)$ count the pairs $(a,z)\in T\times\mathcal B$ such that $w\in E(a)$, no distinct retained member of $A$ shares either address with $a$, and $w\notin E(b)$ for every $b\in C(a,z)$. Then one common state $w$ satisfies
--   $$
--   8|\Omega|\,M(w)\ge 3|T|\,|\mathcal B|\,K.
--   $$
--   The conclusion concerns aggregate surviving incidence mass. It assumes no independence between deletions and does not require a seven-eighths nonhole fraction for every individual target. Empty target or block sets and zero-valued parameters are allowed; the conclusion uses no division.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS2, Section 6.2, Claim 6.8 and equation (24). New finite counting lemma implementing simultaneous X/Y isolation and aggregate nonhole-mass selection in one hash probability space; not a separately numbered statement in the paper.

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

open BigOperators

set_option autoImplicit false

theorem mme_dwz_joint_hash_ambient_xy_isolation_nonhole_mass
    {State Edge Block X Y : Type*}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [Fintype Edge] [DecidableEq Edge]
    [Fintype Block] [DecidableEq Block] [DecidableEq X] [DecidableEq Y]
    (targets ambient : Finset Edge) (events : Edge → Finset State)
    (x : Edge → X) (y : Edge → Y)
    (zCompetitors : Edge → Block → Finset Edge)
    (K J p d c : ℕ) (hK : K = p * J)
    (hxyBudget : 4 * d ≤ p) (hzBudget : 8 * c ≤ p)
    (hsingle : ∀ a ∈ targets, (events a).card = K)
    (hx : ∀ a ∈ targets, (ambient.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ targets, (ambient.filter (fun b ↦ y b = y a)).card ≤ d)
    (hzCard : ∀ a ∈ targets, ∀ z, (zCompetitors a z).card ≤ c)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient,
      b ≠ a → (x b = x a ∨ y b = y a) →
        (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z, ∀ b ∈ zCompetitors a z,
      (events a ∩ events b).card ≤ J) :
    ∃ w : State,
      3 * (targets.card * Fintype.card Block * K) ≤
        8 * (Fintype.card State *
          ((targets.product Finset.univ).filter (fun az ↦
            w ∈ events az.1 ∧
              (∀ b ∈ ambient, w ∈ events b →
                (x b = x az.1 ∨ y b = y az.1) → b = az.1) ∧
              ∀ b ∈ zCompetitors az.1 az.2, w ∉ events b)).card) := by sorry
