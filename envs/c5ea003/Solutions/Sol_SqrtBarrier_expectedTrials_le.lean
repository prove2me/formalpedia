-- Prove2me | solution 1 for SqrtBarrier.expectedTrials_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:08:31.918018+00:00
-- url     : https://prove2.me/submissions/320279aa-fc97-4e49-973a-095036377192

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





/-- With equal root counts `h` (the class-number case) the count is exactly
`h (p + q - 2h)`. -/
theorem card_goodPairs_balanced (Rp : Finset (ZMod p)) (Rq : Finset (ZMod q)) (h : ℕ)
    (hp : Rp.card = h) (hq : Rq.card = h) (hph : h ≤ p) (hqh : h ≤ q) :
    (goodPairs Rp Rq).card = h * (p + q - 2 * h) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hph
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hqh
  rw [card_goodPairs, hp, hq]
  have e1 : h + a - h = a := by omega
  have e2 : h + b - h = b := by omega
  have e3 : h + a + (h + b) - 2 * h = a + b := by omega
  rw [e1, e2, e3]
  ring

/-- Lower bound on the count in the equal-root-count case. -/
theorem card_goodPairs_ge (Rp : Finset (ZMod p)) (Rq : Finset (ZMod q)) (h : ℕ)
    (hp : Rp.card = h) (hq : Rq.card = h) (h4p : 4 * h ≤ p) (h4q : 4 * h ≤ q) :
    h * (p + q) ≤ 2 * (goodPairs Rp Rq).card := by
  rw [card_goodPairs_balanced Rp Rq h hp hq (by omega) (by omega)]
  have : p + q ≤ 2 * (p + q - 2 * h) := by omega
  calc h * (p + q) ≤ h * (2 * (p + q - 2 * h)) := Nat.mul_le_mul_left _ this
    _ = 2 * (h * (p + q - 2 * h)) := by ring



/-! ## Expected number of evaluations -/



private lemma sqrt_le_avg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Real.sqrt (p * q) ≤ (p + q) / 2 := by
  have h0 : (0:ℝ) ≤ p * q := by nlinarith
  have hs := Real.sq_sqrt h0
  have hnn := Real.sqrt_nonneg (p * q)
  nlinarith [hs, hnn, sq_nonneg (p - q), sq_nonneg (Real.sqrt (p * q) - (p + q) / 2)]





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
theorem solution(Rp : Finset (ZMod p)) (Rq : Finset (ZMod q)) (h : ℕ)
    (hp : Rp.card = h) (hq : Rq.card = h) (hh : 0 < h) (h4p : 4 * h ≤ p) (h4q : 4 * h ≤ q) :
    expectedTrials Rp Rq ≤ Real.sqrt (p * q) / h := by
  have hp0 : (0:ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hq0 : (0:ℝ) < q := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hh0 : (0:ℝ) < h := by exact_mod_cast hh
  -- 2|G| ≥ h (p+q) ≥ 2 h √(pq)
  have h1 : (h : ℝ) * (p + q) ≤ 2 * (goodPairs Rp Rq).card := by
    exact_mod_cast card_goodPairs_ge Rp Rq h hp hq h4p h4q
  have h2 : Real.sqrt ((p:ℝ) * q) ≤ ((p:ℝ) + q) / 2 :=
    sqrt_le_avg (le_of_lt hp0) (le_of_lt hq0)
  have hGge : (h : ℝ) * Real.sqrt ((p:ℝ) * q) ≤ (goodPairs Rp Rq).card := by nlinarith
  have hs0 : 0 < Real.sqrt ((p:ℝ) * q) := Real.sqrt_pos.mpr (by positivity)
  have hG0 : (0:ℝ) < (goodPairs Rp Rq).card := lt_of_lt_of_le (by positivity) hGge
  rw [expectedTrials, div_le_div_iff₀ hG0 hh0]
  have hsq : Real.sqrt ((p:ℝ) * q) * Real.sqrt ((p:ℝ) * q) = (p:ℝ) * q :=
    Real.mul_self_sqrt (by positivity)
  nlinarith [hGge, hs0, hsq]
