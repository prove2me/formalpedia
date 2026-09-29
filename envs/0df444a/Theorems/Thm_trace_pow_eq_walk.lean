-- Prove2me | Theorems.Thm_trace_pow_eq_walk
-- name    : trace_pow_eq_walk
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T21:11:12.514295+00:00
-- url     : https://prove2.me/theorems/978b0172-9123-4c07-9bfc-913c2919f05e
-- statement:
--   For a square matrix $M$ over a commutative ring and any $n \geq 0$, the trace of $M^{n+1}$ equals the sum over all closed walks of length $n+1$ of the product of edge weights along the walk:
--
--   $$\operatorname{tr}(M^{n+1}) = \sum_{v : \{0,\dots,n\} \to \iota} \prod_{k=0}^{n} M_{v(k),\,v(k+1 \bmod (n+1))}.$$
--
--   Here a *closed walk* of length $n+1$ is a function $v$ from the cyclic index set $\mathbb{Z}/(n+1)$ to the vertex set $\iota$, and the successor index is taken modulo $n+1$ (so the walk returns to its start). This is the standard combinatorial expansion of trace moments as a sum over closed walks, the entry point of the moment method (Buchholz, *Operator Khintchine inequality in non-commutative probability*, Math. Ann. 319 (2001) 1–16, §2).
-- source:
--   Buchholz, Operator Khintchine inequality in non-commutative probability, Math. Ann. 319 (2001) 1-16, section 2; CR2009 (arXiv:0805.4471) section 6.1 Lemma 6.1

import Mathlib
open Matrix
open scoped BigOperators

theorem trace_pow_eq_walk {iota : Type*} [Fintype iota] [DecidableEq iota]
    {R : Type*} [CommRing R] (M : Matrix iota iota R) (n : Nat) :
    Matrix.trace (M ^ (n + 1)) =
      ∑ v : Fin (n + 1) → iota,
        ∏ k : Fin (n + 1),
          M (v k) (v ⟨(k.1 + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩) := by sorry
