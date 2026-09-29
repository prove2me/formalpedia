-- Prove2me | solution 1 for CollisionBarrier.scheme_reveals_few_primes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:08:45.60072+00:00
-- url     : https://prove2.me/submissions/3f5a5974-4477-4afe-87b7-328fd948cf8e

-- Sol generated from Shared/CollisionSchemeUniversalBarrier.lean
import Mathlib
import Definitions.Def_Shared_CollisionSchemeUniversalBarrier

/-!
# A universal barrier for collision-based factoring schemes

The previous files analysed specific rows of the birthday-bound hierarchy
(sumset, 3SUM, `r`-SUM, structured evaluations).  Here we abstract away the way
values are produced and keep only what all of them share: a finite *search
space* together with a *value map* into `ℕ`, and the rule that a factor is
extracted as `gcd (difference of two values) N`.

Two universal theorems are proved for this abstraction.

**Span barrier** (`reveals_le_span`).  If such a scheme reveals a factor `f`
of `N`, then two of its values differ by at least `f`.  For a semiprime
`N = p * q` with `q ≤ p` and `f = p`, this forces the scheme to manipulate
numbers of size at least `√N`: no scheme whose values live in a short interval
can ever factor, whatever its arity or internal structure.

**Coverage barrier** (`scheme_reveals_few_primes`).  A *fixed* scheme reveals
very few large primes: with `k` search points and values below `B`, at most
`log_P B · k²` primes `≥ P` can divide any of its `≤ k²` pairwise differences.
Hence a scheme that must succeed on `T` different semiprimes with larger factor
`≥ P` needs `k² ≥ T / log_P B`.  The exponent games of the hierarchy change how
`k` relates to arity, but never this counting bound.

Main results:

* `reveals_le_span`, `reveals_sqrt_barrier` — the span barrier.
* `pow_card_le_of_primes_dvd` — `P ^ |Q| ≤ d` for distinct primes `≥ P`
  dividing `d`.
* `card_le_log_of_primes_dvd` — hence `|Q| ≤ log_P d`.
* `scheme_reveals_few_primes` — the coverage barrier.
* `scheme_space_lower_bound` — its contrapositive cost form.
-/

open CollisionBarrier

open Finset


variable {α : Type*}


theorem card_diffs_le [DecidableEq α] (C : Scheme α) :
    (diffs C).card ≤ C.space.card ^ 2 := by
  calc (diffs C).card ≤ (C.space ×ˢ C.space).card := Finset.card_image_le
    _ = C.space.card ^ 2 := by rw [Finset.card_product, sq]


/-! ## The span barrier -/




/-! ## The coverage barrier -/

/-- If `Q` is a set of distinct primes, all at least `P`, all dividing a
positive `d`, then `P ^ |Q| ≤ d`. -/
theorem pow_card_le_of_primes_dvd {P d : ℕ} {Q : Finset ℕ} (hd : 0 < d)
    (hprime : ∀ p ∈ Q, p.Prime) (hge : ∀ p ∈ Q, P ≤ p) (hdvd : ∀ p ∈ Q, p ∣ d) :
    P ^ Q.card ≤ d := by
  have hprod : (∏ p ∈ Q, p) ∣ d :=
    Finset.prod_primes_dvd d (fun a ha => (hprime a ha).prime) hdvd
  calc P ^ Q.card = ∏ _p ∈ Q, P := by simp
    _ ≤ ∏ p ∈ Q, p := Finset.prod_le_prod' hge
    _ ≤ d := Nat.le_of_dvd hd hprod

/-- Logarithmic form: a positive integer `d` has at most `log_P d` distinct
prime divisors `≥ P`. -/
theorem card_le_log_of_primes_dvd {P d : ℕ} {Q : Finset ℕ} (hP : 1 < P)
    (hd : 0 < d) (hprime : ∀ p ∈ Q, p.Prime) (hge : ∀ p ∈ Q, P ≤ p)
    (hdvd : ∀ p ∈ Q, p ∣ d) : Q.card ≤ Nat.log P d :=
  (Nat.le_log_iff_pow_le hP hd.ne').mpr (pow_card_le_of_primes_dvd hd hprime hge hdvd)




open CollisionBarrier in
theorem solution[DecidableEq α] (C : Scheme α) {P B : ℕ}
    (hP : 1 < P) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ P ≤ p ∧
      ∃ d ∈ diffs C, 0 < d ∧ d ≤ B ∧ p ∣ d) :
    Q.card ≤ Nat.log P B * C.space.card ^ 2 := by
  classical
  -- choose, for every `p ∈ Q`, a difference of the scheme divisible by `p`
  set g : ℕ → ℕ := fun p => if h : p ∈ Q then (hQ p h).2.2.choose else 0 with hg
  have hgspec : ∀ p ∈ Q, g p ∈ diffs C ∧ 0 < g p ∧ g p ≤ B ∧ p ∣ g p := by
    intro p hp
    have := (hQ p hp).2.2.choose_spec
    simpa [hg, hp] using this
  -- each difference accounts for at most `log_P B` primes
  have hfiber : ∀ b ∈ Q.image g, {a ∈ Q | g a = b}.card ≤ Nat.log P B := by
    intro b hb
    rcases Finset.eq_empty_or_nonempty {a ∈ Q | g a = b} with hemp | ⟨p₀, hp₀⟩
    · simp [hemp]
    · simp only [Finset.mem_filter] at hp₀
      obtain ⟨hp₀Q, hp₀g⟩ := hp₀
      have hb0 : 0 < b := hp₀g ▸ (hgspec _ hp₀Q).2.1
      have hbB : b ≤ B := hp₀g ▸ (hgspec _ hp₀Q).2.2.1
      have hcard : {a ∈ Q | g a = b}.card ≤ Nat.log P b := by
        refine card_le_log_of_primes_dvd hP hb0 ?_ ?_ ?_ <;>
          intro p hp <;> simp only [Finset.mem_filter] at hp
        · exact (hQ p hp.1).1
        · exact (hQ p hp.1).2.1
        · exact hp.2 ▸ (hgspec p hp.1).2.2.2
      exact le_trans hcard (Nat.log_mono_right hbB)
  have himg : (Q.image g).card ≤ C.space.card ^ 2 := by
    refine le_trans (Finset.card_le_card ?_) (card_diffs_le C)
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact (hgspec p hp).1
  calc Q.card ≤ Nat.log P B * (Q.image g).card :=
        Finset.card_le_mul_card_image Q _ hfiber
    _ ≤ Nat.log P B * C.space.card ^ 2 := Nat.mul_le_mul_left _ himg
