-- Prove2me | solution 1 for SqrtBarrier.success_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:08:33.095279+00:00
-- url     : https://prove2.me/submissions/209a0f32-f4d2-4830-bd99-f139fd9814ef

-- Sol generated from Geometry/SingularModuliBarrier.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliBarrier
import Theorems.Thm_SqrtBarrier_card_goodPairs
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
theorem solution(Rp : Finset (ZMod p)) (Rq : Finset (ZMod q)) (d T : ℕ)
    (hdp : Rp.card ≤ d) (hdq : Rq.card ≤ d) (hd : 0 < d)
    (hpq : p ≤ q) (hbal : q ≤ 2 * p) :
    1 - (1 - ((goodPairs Rp Rq).card : ℝ) / (p * q)) ^ T
      ≤ (T : ℝ) * (3 * d) / Real.sqrt (p * q) := by
  have hp0 : (0:ℝ) < p := by
    have := Nat.pos_of_ne_zero (NeZero.ne p); exact_mod_cast this
  have hq0 : (0:ℝ) < q := by
    have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  set x : ℝ := ((goodPairs Rp Rq).card : ℝ) / (p * q) with hx
  have hGle : ((goodPairs Rp Rq).card : ℝ) ≤ d * ((p:ℝ) + q) := by
    exact_mod_cast card_goodPairs_le Rp Rq d hdp hdq
  have h2 : (p : ℝ) + q ≤ 3 * p := by
    have : (q:ℝ) ≤ 2 * p := by exact_mod_cast hbal
    linarith
  have h3 : (p : ℝ) ≤ Real.sqrt (p * q) :=
    sqrt_ge_left (le_of_lt hp0) (by exact_mod_cast hpq)
  have hs0 : 0 < Real.sqrt ((p:ℝ) * q) := lt_of_lt_of_le hp0 h3
  have hsq : Real.sqrt ((p:ℝ) * q) * Real.sqrt ((p:ℝ) * q) = (p:ℝ) * q :=
    Real.mul_self_sqrt (by positivity)
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by
    have hcard : Fintype.card (ZMod p × ZMod q) = p * q := by
      simp [Fintype.card_prod, ZMod.card]
    have hle := Finset.card_le_univ (goodPairs Rp Rq)
    rw [hcard] at hle
    have : ((goodPairs Rp Rq).card : ℝ) ≤ (p : ℝ) * q := by exact_mod_cast hle
    rw [hx, div_le_one (by positivity)]
    exact this
  -- Bernoulli: 1 - T x ≤ (1 - x)^T
  have hbern : 1 - (T : ℝ) * x ≤ (1 - x) ^ T := by
    have := one_add_mul_le_pow (a := -x) (by linarith) T
    simpa [sub_eq_add_neg, mul_comm] using this
  -- x ≤ 3 d / √N
  have hxle : x ≤ 3 * d / Real.sqrt ((p:ℝ) * q) := by
    have hA : ((goodPairs Rp Rq).card : ℝ) * Real.sqrt ((p:ℝ) * q)
        ≤ (3 * d * p) * Real.sqrt ((p:ℝ) * q) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hGle, h2, hd0]) (le_of_lt hs0)
    have hB : (p : ℝ) * Real.sqrt ((p:ℝ) * q) ≤ (p:ℝ) * q := by nlinarith [h3, hsq, hs0]
    rw [hx, div_le_div_iff₀ (by positivity) hs0]
    nlinarith [hA, hB, hd0]
  have hT0 : (0:ℝ) ≤ T := by positivity
  calc 1 - (1 - x) ^ T ≤ (T : ℝ) * x := by linarith
    _ ≤ (T : ℝ) * (3 * d / Real.sqrt ((p:ℝ) * q)) := by
        exact mul_le_mul_of_nonneg_left hxle hT0
    _ = (T : ℝ) * (3 * d) / Real.sqrt ((p:ℝ) * q) := by ring
