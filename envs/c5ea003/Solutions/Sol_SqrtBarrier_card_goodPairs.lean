-- Prove2me | solution 1 for SqrtBarrier.card_goodPairs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:58:02.738511+00:00
-- url     : https://prove2.me/submissions/5fd95f48-17a3-4e43-abd3-e111a713f37f

-- Sol generated from Geometry/SingularModuliBarrier.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliBarrier
/-
# The √N Barrier for Structured-Set Factoring (abstract layer)

Companion to `SingularModuliCore.lean`.  That file shows that for a semiprime
`N = p q` and an integer polynomial `f` (e.g. a Hilbert class polynomial `H_D`)
the evaluation point `j₀` factors `N` **iff** its CRT coordinates lie in the
"exclusive-or" set

    G = { (a,b) : a ∈ R_p, b ∉ R_q } ∪ { (a,b) : a ∉ R_p, b ∈ R_q },

where `R_m` is the root set of `f` mod `m`.  Here we forget the polynomial
entirely and analyse this configuration for *arbitrary* subsets
`R_p ⊆ ZMod p`, `R_q ⊆ ZMod q` with `|R_p|, |R_q| ≤ d`.  This is the honest
level of generality: the only feature of singular moduli the method exploits is
that `H_D` has few roots (`h(D) = deg H_D`) modulo each prime.

Main results.

* `SqrtBarrier.card_goodPairs` — the exact count `r_p (q - r_q) + (p - r_p) r_q`.
* `SqrtBarrier.expectedTrials_ge` — **lower bound**: for balanced primes
  (`p ≤ q ≤ 2p`) and root counts `≤ d`, the expected number of uniformly random
  evaluation points before a factor is found is at least `√N / (3 d)`.
* `SqrtBarrier.expectedTrials_le` — **matching upper bound**: if both root
  counts equal `h ≥ 1` and `4h ≤ p`, the expectation is at most `√N / h`.
  Hence the method is `Θ(√N / h)` — it *works*, and it is *exponential in the
  bit size of N*, quantified in `SqrtBarrier.expectedTrials_ge_two_pow`.
* `SqrtBarrier.exists_bad_shift` and `SqrtBarrier.exists_bad_shift_of_small`
  — **the circularity barrier**, in an adversarial (not merely probabilistic)
  form: a translation-averaging argument shows that *any* fixed query set of
  size below `√N / (3 d)` is defeated by some translate of the structured set.
  Knowing that the target set is "structured" is worth nothing unless one knows
  *where* it is, which is exactly the information `p` encodes.

Note on the informal claim `√N/(4h)` in the source note: the exact count below
gives expectation `pq / (h (p + q - 2h))`, i.e. `≈ √N / (2h)` for balanced
primes, not `√N/(4h)`.  The heuristic there double-counts the two primes; the
corrected constant is proved in `expectedTrials_balanced_eq`.
-/

open SqrtBarrier

open Finset

variable {p q : ℕ} [NeZero p] [NeZero q]

/-! ## The exclusive-or configuration and its exact size -/









/-! ## Expected number of evaluations -/








/-! ## Random search: a rigorous success-probability bound

`expectedTrials` above is the mean of the geometric distribution.  To avoid
leaning on that interpretation, this section proves the corresponding statement
purely by counting: among all `N^T` sequences of `T` independent uniform
evaluation points, the proportion on which *every* point fails is
`(1 - |G|/N)^T`, and hence the success probability of a `T`-point random search
is at most `3 d T / √N`.  Below `√N/(6d)` points it is less than one half. -/




/-! ## The circularity barrier: averaging over translates -/








/-! ## Families of discriminants: the class-number gain is illusory

The informal claim `√N/(4h)` suggests that using class polynomials of large
class number `h` buys a factor `h`.  It does not, once one is honest about
*which* discriminants are useful.  `H_D` has `h(D)` roots mod `p` only when `p`
splits completely in the ring class field, which happens for a proportion
`1/h(D)` of primes (for the other primes there may be no root at all, and then
that discriminant is useless — see `ComputationalEvidence.md`, where
`N = 8051`, `D = -15` gives a *completely empty* success set).  By Chebotarev
the **average** number of roots of an irreducible polynomial modulo `p` is `1`,
independently of its degree; this is the hypothesis `hSp`, `hSq` below with
`c = 1`.  Under it, running a whole family of `k` discriminants costs the same
`Ω(√N)` as a single one: the class number cancels exactly. -/





open SqrtBarrier in
theorem solution(Rp : Finset (ZMod p)) (Rq : Finset (ZMod q)) :
    (goodPairs Rp Rq).card = Rp.card * (q - Rq.card) + (p - Rp.card) * Rq.card := by
  classical
  have h : goodPairs Rp Rq = (Rp ×ˢ Rqᶜ) ∪ (Rpᶜ ×ˢ Rq) := by
    ext ⟨a, b⟩
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product, Finset.mem_compl, Xor]
    tauto
  have hdisj : Disjoint (Rp ×ˢ Rqᶜ) (Rpᶜ ×ˢ Rq) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_compl] at h1 h2
    exact h2.1 h1.1
  rw [h, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    Finset.card_compl, Finset.card_compl, ZMod.card, ZMod.card]
