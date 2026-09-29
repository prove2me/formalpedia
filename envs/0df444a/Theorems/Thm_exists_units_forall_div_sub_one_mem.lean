-- Prove2me | Theorems.Thm_exists_units_forall_div_sub_one_mem
-- name    : exists_units_forall_div_sub_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/ce1b826f-8935-54ea-a63f-2dae861237b5
-- title:
--   Completeness of the unit filtration attached to a shrinking chain of additive subgroups
-- statement:
--   Let $L$ be a complete normed field and let $M \colon \mathbb{N} \to$ (additive subgroups of $L$) be a family such that each $M_n$ is closed as a subset of $L$; the family is antitone, so $M_m \subseteq M_n$ whenever $n \le m$; $x \cdot y \in M_n$ whenever $x \in M_n$ and $y \in M_0$; every $x \in M_0$ has $\|x\| < 1$; and for every $\varepsilon > 0$ there is an $n$ with $\|x\| < \varepsilon$ for all $x \in M_n$. Let $(s_n)_{n \in \mathbb{N}}$ be a sequence of units of $L$ such that for every $n$ both $s_{n+1}/s_n - 1$ and $s_n/s_{n+1} - 1$ (the quotients taken in $L^\times$ and then viewed in $L$) lie in $M_n$. The conclusion is that there exists a unit $x \in L^\times$ such that for every $n$ both $x/s_n - 1 \in M_n$ and $s_n/x - 1 \in M_n$.
--
--   This is the statement that the filtration of $L^\times$ by the subgroups $\{u : u - 1 \in M_n,\ u^{-1} - 1 \in M_n\}$ is complete: a sequence of units whose consecutive ratios converge to $1$ along the filtration has a limit in the same sense. It is used in the successive-approximation construction of a unit-valued cocycle, namely by [`ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle`](thm.html#ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_units_forall_div_sub_one_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_units_forall_div_sub_one_mem
    {L : Type*} [NormedField L] [CompleteSpace L]
    (M : ℕ → AddSubgroup L) (hMclosed : ∀ n, IsClosed (M n : Set L)) (hManti : Antitone M)
    (hMmul : ∀ (n : ℕ) (x y : L), x ∈ M n → y ∈ M 0 → x * y ∈ M n)
    (hMnorm : ∀ x ∈ M 0, ‖x‖ < 1)
    (hMsmall : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ M n, ‖x‖ < ε)
    (s : ℕ → Lˣ)
    (hs : ∀ n, ((s (n + 1) / s n : Lˣ) : L) - 1 ∈ M n ∧ ((s n / s (n + 1) : Lˣ) : L) - 1 ∈ M n) :
    ∃ x : Lˣ, ∀ n, ((x / s n : Lˣ) : L) - 1 ∈ M n ∧ ((s n / x : Lˣ) : L) - 1 ∈ M n := by sorry
