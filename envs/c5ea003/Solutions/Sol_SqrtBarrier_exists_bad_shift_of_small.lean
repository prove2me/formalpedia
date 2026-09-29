-- Prove2me | solution 1 for SqrtBarrier.exists_bad_shift_of_small
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:03:09.360737+00:00
-- url     : https://prove2.me/submissions/0f983641-1511-4ca7-85a3-41a7506c04b4

-- Sol generated from Geometry/SingularModuliBarrier.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliBarrier
import Theorems.Thm_SqrtBarrier_card_goodPairs
import Theorems.Thm_SqrtBarrier_exists_bad_shift_general
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



/-- Few roots ⟹ few successful residues: `|G| ≤ d (p + q)`. -/
theorem card_goodPairs_le (Rp : Finset (ZMod p)) (Rq : Finset (ZMod q)) (d : ℕ)
    (hp : Rp.card ≤ d) (hq : Rq.card ≤ d) :
    (goodPairs Rp Rq).card ≤ d * (p + q) := by
  rw [card_goodPairs]
  calc Rp.card * (q - Rq.card) + (p - Rp.card) * Rq.card
      ≤ Rp.card * q + p * Rq.card := by
        gcongr <;> omega
    _ ≤ d * q + p * d := by gcongr
    _ = d * (p + q) := by ring






/-! ## Expected number of evaluations -/


private lemma sqrt_ge_left {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) : p ≤ Real.sqrt (p * q) := by
  have h0 : (0:ℝ) ≤ p * q := by nlinarith
  have hs := Real.sq_sqrt h0
  have hnn := Real.sqrt_nonneg (p * q)
  nlinarith [hs, hnn, sq_nonneg (Real.sqrt (p * q) - p)]






/-! ## Random search: a rigorous success-probability bound

`expectedTrials` above is the mean of the geometric distribution.  To avoid
leaning on that interpretation, this section proves the corresponding statement
purely by counting: among all `N^T` sequences of `T` independent uniform
evaluation points, the proportion on which *every* point fails is
`(1 - |G|/N)^T`, and hence the success probability of a `T`-point random search
is at most `3 d T / √N`.  Below `√N/(6d)` points it is less than one half. -/




/-! ## The circularity barrier: averaging over translates -/




/-- Specialisation of `exists_bad_shift_general` to the success set of a class
polynomial. -/
theorem exists_bad_shift (Rp : Finset (ZMod p)) (Rq : Finset (ZMod q))
    (S : Finset (ZMod p × ZMod q))
    (hS : S.card * (goodPairs Rp Rq).card < p * q) :
    ∃ t : ZMod p × ZMod q, ∀ s ∈ S, t + s ∉ goodPairs Rp Rq :=
  exists_bad_shift_general (goodPairs Rp Rq) S hS




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
theorem solution(Rp : Finset (ZMod p)) (Rq : Finset (ZMod q))
    (S : Finset (ZMod p × ZMod q)) (d : ℕ)
    (hdp : Rp.card ≤ d) (hdq : Rq.card ≤ d) (hd : 0 < d)
    (hpq : p ≤ q) (hbal : q ≤ 2 * p)
    (hsmall : (S.card : ℝ) * (3 * d) < Real.sqrt (p * q)) :
    ∃ t : ZMod p × ZMod q, ∀ s ∈ S, t + s ∉ goodPairs Rp Rq := by
  refine exists_bad_shift Rp Rq S ?_
  have hp0 : (0:ℝ) < p := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); exact_mod_cast this
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have h1 : ((goodPairs Rp Rq).card : ℝ) ≤ d * (p + q) := by
    exact_mod_cast card_goodPairs_le Rp Rq d hdp hdq
  have h2 : (p : ℝ) + q ≤ 3 * p := by
    have : (q:ℝ) ≤ 2 * p := by exact_mod_cast hbal
    linarith
  have h3 : (p : ℝ) ≤ Real.sqrt (p * q) :=
    sqrt_ge_left (le_of_lt hp0) (by exact_mod_cast hpq)
  have hGle : ((goodPairs Rp Rq).card : ℝ) ≤ 3 * d * Real.sqrt (p * q) := by nlinarith
  have hsq : Real.sqrt ((p:ℝ) * q) * Real.sqrt ((p:ℝ) * q) = (p:ℝ) * q :=
    Real.mul_self_sqrt (by positivity)
  have hS0 : (0:ℝ) ≤ (S.card : ℝ) := by positivity
  have key : ((S.card * (goodPairs Rp Rq).card : ℕ) : ℝ) < ((p * q : ℕ) : ℝ) := by
    push_cast
    calc (S.card : ℝ) * (goodPairs Rp Rq).card
        ≤ (S.card : ℝ) * (3 * d * Real.sqrt (p * q)) := by nlinarith
      _ = ((S.card : ℝ) * (3 * d)) * Real.sqrt (p * q) := by ring
      _ < Real.sqrt ((p:ℝ) * q) * Real.sqrt ((p:ℝ) * q) := by
          have hs0 : 0 < Real.sqrt ((p:ℝ) * q) := lt_of_lt_of_le hp0 h3
          exact (mul_lt_mul_of_pos_right hsmall hs0)
      _ = (p : ℝ) * q := hsq
  exact_mod_cast key
