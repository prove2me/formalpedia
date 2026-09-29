-- Prove2me | solution 1 for CRTSplitNoGo.successor_reveal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:57:07.499986+00:00
-- url     : https://prove2.me/submissions/21f069d0-1bad-44cc-a00f-b1d63d0916b9

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoBounds

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Bridges/CRTSplitNoGo.lean ====
/-!
# The CRT-Split No-Go, Part I: the reveal mechanism

This file formalises the two structural facts underlying the claim that no classical
iteration built from `N` alone can factor `N = p * q` in `poly(log N)` steps.

* **Fact 1 (CRT-split collision is the only reveal mechanism).**
  For `N = p * q` with `p ≠ q` prime and any integer `d`,
  `gcd d N` is a *nontrivial* divisor of `N` if and only if **exactly one** of
  `p ∣ d`, `q ∣ d` holds (`crt_reveal_iff`).  Applied to `d = x t - x s` along a
  trajectory this says: a factor appears exactly when two trajectory values agree
  on **one** CRT component.

* **Fact 2 (`N`-explicit maps do not split the CRT).**
  An `N`-explicit map is a polynomial with integer coefficients (ring operations and
  constants manufactured from the digits of `N`).  Its orbit reduced mod `p` is the
  orbit of the *reduced* polynomial started at the *reduced* seed
  (`polyOrbit_cast`, `modOrbit_congr`): the mod-`p` dynamics depends on nothing
  except `f mod p` and `x₀ mod p`.  In particular the map itself carries no
  information about which of the two CRT components it is being run in.

* **Consequence.** The factor-revealing event in any such iteration is *exactly* an
  exclusive mod-`p` / mod-`q` cycle closure (`reveal_iff_xor_closure`), and no reveal
  can happen before the first closure (`no_reveal_before_closure`).  Closures do
  exist, but the only unconditional guarantee is the pigeonhole bound `t ≤ p`
  (`exists_closure_le`), and after a closure the orbit is eventually periodic
  (`modOrbit_eventually_periodic`) — the rho shape.

Quantitative lower bounds for the three regimes are in `CRTSplitNoGoBounds.lean`.
-/

namespace CRTSplitNoGo

open Polynomial

/-! ## Fact 1: a nontrivial gcd is exactly an exclusive CRT collision -/

-- [dropped: platform already declares RevealsFactor]
lemma dvd_gcd_iff_of_dvd {N : ℕ} {d : ℤ} {r : ℕ} (hrN : r ∣ N) :
    r ∣ Int.gcd d (N : ℤ) ↔ (r : ℤ) ∣ d := by
  constructor
  · intro h
    have : ((r : ℕ) : ℤ) ∣ ((Int.gcd d (N : ℤ) : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    exact this.trans (Int.gcd_dvd_left d (N : ℤ))
  · intro h
    have hrN' : (r : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hrN
    exact Int.dvd_gcd h hrN'

/-- **Fact 1.**  With `N = p * q` a product of two distinct primes, `d` reveals a
nontrivial factor of `N` if and only if exactly one of `p`, `q` divides `d`. -/
theorem crt_reveal_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (d : ℤ) :
    RevealsFactor (p * q) d ↔ Xor' ((p : ℤ) ∣ d) ((q : ℤ) ∣ d) := by
  have hppos : 0 < p := hp.pos
  have hqpos : 0 < q := hq.pos
  have hNpos : 0 < p * q := Nat.mul_pos hppos hqpos
  set g : ℕ := Int.gcd d ((p * q : ℕ) : ℤ) with hg
  have hgN : g ∣ p * q := by
    have : ((g : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ) := Int.gcd_dvd_right d ((p * q : ℕ) : ℤ)
    exact Int.ofNat_dvd.mp this
  have hgle : g ≤ p * q := Nat.le_of_dvd hNpos hgN
  have hpdvdN : p ∣ p * q := Dvd.intro q rfl
  have hqdvdN : q ∣ p * q := Dvd.intro_left p rfl
  have hP : p ∣ g ↔ (p : ℤ) ∣ d := dvd_gcd_iff_of_dvd hpdvdN
  have hQ : q ∣ g ↔ (q : ℤ) ∣ d := dvd_gcd_iff_of_dvd hqdvdN
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  rw [← hP, ← hQ]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hpg : p ∣ g
    · refine Or.inl ⟨hpg, ?_⟩
      intro hqg
      have : p * q ∣ g := hcop.mul_dvd_of_dvd_of_dvd hpg hqg
      have := Nat.le_of_dvd (by omega) this
      omega
    · by_cases hqg : q ∣ g
      · exact Or.inr ⟨hqg, hpg⟩
      · -- neither prime divides `g`, so `g` is coprime to `N` and hence `g = 1`
        exfalso
        have hcp : Nat.Coprime g p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpg))
        have hcq : Nat.Coprime g q := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqg))
        have : Nat.Coprime g (p * q) := Nat.Coprime.mul_right hcp hcq
        have hg1 : g = 1 := this.eq_one_of_dvd hgN
        omega
  · intro h
    rcases h with ⟨hpg, hqg⟩ | ⟨hqg, hpg⟩
    · have hgpos : 0 < g := by
        rcases Nat.eq_zero_or_pos g with h0 | h0
        · exfalso; rw [h0] at hgN; exact absurd (Nat.eq_zero_of_zero_dvd hgN) (by omega)
        · exact h0
      have h1 : 1 < g := lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hpg)
      refine ⟨h1, ?_⟩
      rcases lt_or_eq_of_le hgle with h | h
      · exact h
      · exact absurd (h ▸ hqdvdN) hqg
    · have hgpos : 0 < g := by
        rcases Nat.eq_zero_or_pos g with h0 | h0
        · exfalso; rw [h0] at hgN; exact absurd (Nat.eq_zero_of_zero_dvd hgN) (by omega)
        · exact h0
      have h1 : 1 < g := lt_of_lt_of_le hq.one_lt (Nat.le_of_dvd hgpos hqg)
      refine ⟨h1, ?_⟩
      rcases lt_or_eq_of_le hgle with h | h
      · exact h
      · exact absurd (h ▸ hpdvdN) hpg

/-! ## Fact 2: an `N`-explicit map is functorial for reduction mod `p` -/

/-- The orbit of the seed `x₀` under the integer polynomial map `f`. -/
-- [dropped: platform already declares polyOrbit]
@[simp] lemma polyOrbit_zero (f : ℤ[X]) (x0 : ℤ) : polyOrbit f x0 0 = x0 := rfl

lemma polyOrbit_succ (f : ℤ[X]) (x0 : ℤ) (n : ℕ) :
    polyOrbit f x0 (n + 1) = f.eval (polyOrbit f x0 n) := by
  simp [polyOrbit, Function.iterate_succ_apply']

/-- The orbit of the reduced seed under the reduced polynomial map, in `ZMod m`. -/
-- [dropped: platform already declares modOrbit]
lemma modOrbit_succ (f : ℤ[X]) (m : ℕ) (x0 : ℤ) (n : ℕ) :
    modOrbit f m x0 (n + 1) =
      (f.map (Int.castRingHom (ZMod m))).eval (modOrbit f m x0 n) := by
  simp [modOrbit, Function.iterate_succ_apply']

/-- **Fact 2 (functoriality).** Reducing the integer orbit mod `m` gives the orbit of the
reduced polynomial: the mod-`m` dynamics is computed entirely inside `ZMod m`. -/
theorem polyOrbit_cast (f : ℤ[X]) (m : ℕ) (x0 : ℤ) (n : ℕ) :
    ((polyOrbit f x0 n : ℤ) : ZMod m) = modOrbit f m x0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [polyOrbit_succ, modOrbit_succ, ← ih]
      simp [Polynomial.eval_map]

/-- **Fact 2 (blindness).** The mod-`m` orbit depends only on the reduction of the map and
of the seed: two `N`-explicit maps whose coefficients agree mod `m`, started at seeds
congruent mod `m`, have identical mod-`m` orbits.  A map "built from `N`" therefore
cannot behave differently in the two CRT components. -/
theorem modOrbit_congr {f g : ℤ[X]} {m : ℕ} {x0 y0 : ℤ}
    (hfg : f.map (Int.castRingHom (ZMod m)) = g.map (Int.castRingHom (ZMod m)))
    (hxy : ((x0 : ℤ) : ZMod m) = ((y0 : ℤ) : ZMod m)) (n : ℕ) :
    modOrbit f m x0 n = modOrbit g m y0 n := by
  unfold modOrbit
  rw [hfg, hxy]

/-- Congruent seeds give congruent trajectories: the classical "no CRT split" statement
in divisibility form. -/
theorem dvd_sub_polyOrbit_of_dvd_sub (f : ℤ[X]) (m : ℤ) {x0 y0 : ℤ} (h : m ∣ x0 - y0) (n : ℕ) :
    m ∣ polyOrbit f x0 n - polyOrbit f y0 n := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [polyOrbit_succ, polyOrbit_succ]
      exact ih.trans (Polynomial.sub_dvd_eval_sub _ _ f)

/-! ## Consequence: the reveal event is an exclusive mod-`p` cycle closure -/

lemma intCast_sub_eq_zero_iff (m : ℕ) (a b : ℤ) :
    ((a : ZMod m) = (b : ZMod m)) ↔ (m : ℤ) ∣ a - b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) m, Int.cast_sub, sub_eq_zero]

/-- **The reveal characterisation.**  Along the orbit of *any* integer polynomial map,
`gcd (x t - x s) N` is a nontrivial factor of `N = p * q` if and only if the mod-`p` orbit
closes up between times `s` and `t` **exclusive-or** the mod-`q` orbit does. -/
theorem reveal_iff_xor_closure {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (f : ℤ[X]) (x0 : ℤ) (s t : ℕ) :
    RevealsFactor (p * q) (polyOrbit f x0 t - polyOrbit f x0 s) ↔
      Xor' (modOrbit f p x0 t = modOrbit f p x0 s)
           (modOrbit f q x0 t = modOrbit f q x0 s) := by
  rw [crt_reveal_iff hp hq hne]
  rw [← intCast_sub_eq_zero_iff p, ← intCast_sub_eq_zero_iff q,
    polyOrbit_cast, polyOrbit_cast, polyOrbit_cast, polyOrbit_cast]

/-- No factor can be revealed before one of the two reduced orbits closes up. -/
theorem no_reveal_before_closure {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (f : ℤ[X]) (x0 : ℤ) (T : ℕ)
    (hpinj : ∀ s t, s < t → t ≤ T → modOrbit f p x0 t ≠ modOrbit f p x0 s)
    (hqinj : ∀ s t, s < t → t ≤ T → modOrbit f q x0 t ≠ modOrbit f q x0 s) :
    ∀ s t, s < t → t ≤ T → ¬ RevealsFactor (p * q) (polyOrbit f x0 t - polyOrbit f x0 s) := by
  intro s t hst htT hrev
  rcases (reveal_iff_xor_closure hp hq hne f x0 s t).mp hrev with ⟨h, -⟩ | ⟨h, -⟩
  · exact hpinj s t hst htT h
  · exact hqinj s t hst htT h

/-! ## The rho shape: closures exist, but pigeonhole only gives `t ≤ p` -/

/-- Pigeonhole: the mod-`p` orbit of any integer polynomial map closes up within `p` steps. -/
theorem exists_closure_le (f : ℤ[X]) (m : ℕ) [NeZero m] (x0 : ℤ) :
    ∃ s t, s < t ∧ t ≤ m ∧ modOrbit f m x0 t = modOrbit f m x0 s := by
  have hcard : Fintype.card (ZMod m) < Fintype.card (Fin (m + 1)) := by
    simp [ZMod.card m]
  obtain ⟨i, j, hij, hval⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (m + 1) => modOrbit f m x0 (i : ℕ)) hcard
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
  · exact ⟨i, j, h, by omega, hval.symm⟩
  · exact ⟨j, i, h, by omega, hval⟩

/-- After a closure at `(s, t)` the reduced orbit is periodic with period `t - s` from time
`s` on: the classical "rho" shape (tail of length `s`, cycle of length `t - s`). -/
theorem modOrbit_eventually_periodic (f : ℤ[X]) (m : ℕ) (x0 : ℤ) {s t : ℕ} (hst : s ≤ t)
    (h : modOrbit f m x0 t = modOrbit f m x0 s) (n : ℕ) (hn : s ≤ n) :
    modOrbit f m x0 (n + (t - s)) = modOrbit f m x0 n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  set F : ZMod m → ZMod m := fun z => (f.map (Int.castRingHom (ZMod m))).eval z with hF
  have key : ∀ j : ℕ, modOrbit f m x0 j = F^[j] ((x0 : ℤ) : ZMod m) := fun j => rfl
  simp only [key] at h ⊢
  have h1 : s + k + (t - s) = k + t := by omega
  rw [h1, Function.iterate_add_apply, h, ← Function.iterate_add_apply, Nat.add_comm]

end CRTSplitNoGo
-- ==== upstream: Packages/Catalog/Bridges/CRTSplitNoGoBounds.lean ====
/-!
# The CRT-Split No-Go, Part II: quantitative barriers and the three regimes

Part I (`CRTSplitNoGo.lean`) showed that for `N = p * q` the factor-revealing event of any
`N`-explicit (i.e. integer-polynomial) iteration is *exactly* an exclusive mod-`p` / mod-`q`
cycle closure.  Here we quantify the cost of such a closure in the three regimes of the
classification, and formalise the circularity barrier.

* **Regime (c), structurally simple maps.**  For the successor map `x ↦ x + 1` the reveal
  time is bounded below by `min p q` (`successor_reveal_lower_bound`), hence by
  `√(N/2)` for balanced semiprimes (`successor_reveal_sqrt_bound`), and — the flagship
  statement — it is **superpolynomial in `log N`**: for every polynomial bound
  `c * (log₂ N)^k` there are semiprimes `N = p q` with `p < q < 2p` on which every reveal
  time exceeds that bound (`successor_reveal_superpolynomial`).

* **Regime (b), smoothness-dependent maps.**  For the Pollard `p-1` style datum `a^M - 1`
  the reveal criterion is exactly an exclusive divisibility of multiplicative orders
  (`pollard_pm1_reveal_iff`), and the exponent `M` must be at least the smaller of the two
  orders (`pollard_pm1_lower_bound`): the cost is governed by the smoothness of
  `ord_p(a)`, a quantity invisible from `N`.

* **Regime (a), generic nonlinear maps.**  Verified on the CTST demo `N = 341371 = 631·541`
  with `f(x) = x² + 1`, seed `2`: the first revealing pair is `(s,t) = (23,36)`, the revealed
  factor is `631`, and this is *exactly* the mod-`631` cycle closure while the mod-`541`
  orbit has not yet closed (`crt_demo_gcd`, `crt_demo_xor`, `crt_demo_closure`).

* **Barrier 6 (circularity).**  Producing a nontrivial CRT idempotent mod `N` *is* factoring
  (`idempotent_reveals`): any map that could separate the CRT components already knows the
  factors.
-/

namespace CRTSplitNoGo

open Polynomial

/-! ## A gcd is insensitive to the modulus -/

lemma gcd_eq_of_dvd_sub {a b : ℤ} {N : ℕ} (h : (N : ℤ) ∣ a - b) :
    Int.gcd a (N : ℤ) = Int.gcd b (N : ℤ) := by
  obtain ⟨k, hk⟩ := h
  have ha : a = b + k * (N : ℤ) := by linarith
  rw [ha, Int.gcd_add_mul_right_left]

lemma revealsFactor_congr {a b : ℤ} {N : ℕ} (h : (N : ℤ) ∣ a - b) :
    RevealsFactor N a ↔ RevealsFactor N b := by
  unfold RevealsFactor
  rw [gcd_eq_of_dvd_sub h]

/-! ## Regime (c): the successor map `x ↦ x + 1` -/

/-- The orbit of the successor map is the arithmetic progression `x₀ + n`. -/
lemma polyOrbit_successor (x0 : ℤ) (n : ℕ) : polyOrbit (X + 1) x0 n = x0 + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [polyOrbit_succ, ih]
      simp only [eval_add, eval_one, eval_X]
      push_cast
      ring

/-- For the successor map the reveal criterion is an exclusive divisibility of the time gap. -/
theorem successor_reveal_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (x0 : ℤ) (s t : ℕ) :
    RevealsFactor (p * q) (polyOrbit (X + 1) x0 t - polyOrbit (X + 1) x0 s) ↔
      Xor' ((p : ℤ) ∣ ((t : ℤ) - s)) ((q : ℤ) ∣ ((t : ℤ) - s)) := by
  rw [crt_reveal_iff hp hq hne]
  simp only [polyOrbit_successor]
  ring_nf

/-- **Regime (c) lower bound.**  A reveal for the successor map forces the time gap to be at
least `min p q`; in particular no reveal is possible before step `min p q`. -/
theorem successor_reveal_lower_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (x0 : ℤ) (s t : ℕ) (hst : s < t)
    (hrev : RevealsFactor (p * q) (polyOrbit (X + 1) x0 t - polyOrbit (X + 1) x0 s)) :
    min p q ≤ t - s := by
  have hpos : (0 : ℤ) < (t : ℤ) - s := by
    have : (s : ℤ) < t := by exact_mod_cast hst
    linarith
  have key : ∀ r : ℕ, (r : ℤ) ∣ ((t : ℤ) - s) → r ≤ t - s := by
    intro r hr
    have h1 : (r : ℤ) ≤ (t : ℤ) - s := Int.le_of_dvd hpos hr
    have h2 : ((t - s : ℕ) : ℤ) = (t : ℤ) - s := by
      have : s ≤ t := le_of_lt hst
      push_cast [Nat.cast_sub this]
      ring
    omega
  rcases (successor_reveal_iff hp hq hne x0 s t).mp hrev with ⟨h, -⟩ | ⟨h, -⟩
  · exact le_trans (min_le_left p q) (key p h)
  · exact le_trans (min_le_right p q) (key q h)

/-- **Regime (c), balanced semiprimes.**  If `p < q < 2p` then any reveal time `t` for the
successor map satisfies `N ≤ 2 t²`, i.e. `t ≥ √(N/2)`: exponential in `log N`. -/
theorem successor_reveal_sqrt_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpq : p < q) (hbal : q ≤ 2 * p) (x0 : ℤ) (s t : ℕ) (hst : s < t)
    (hrev : RevealsFactor (p * q) (polyOrbit (X + 1) x0 t - polyOrbit (X + 1) x0 s)) :
    p * q ≤ 2 * t ^ 2 := by
  have h := successor_reveal_lower_bound hp hq hne x0 s t hst hrev
  have hmin : min p q = p := min_eq_left (le_of_lt hpq)
  rw [hmin] at h
  have hpt : p ≤ t := by omega
  calc p * q ≤ p * (2 * p) := Nat.mul_le_mul_left p hbal
    _ = 2 * (p * p) := by ring
    _ ≤ 2 * (t * t) := by exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul hpt hpt)
    _ = 2 * t ^ 2 := by ring

/-! ### Exponential beats polynomial -/

/-- Eventually `c * L ^ k < 2 ^ L`: the elementary growth fact behind superpolynomiality. -/
lemma eventually_poly_lt_two_pow (c k : ℕ) :
    ∀ᶠ L : ℕ in Filter.atTop, c * L ^ k < 2 ^ L := by
  have h := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k (by norm_num : (1 : ℝ) < 2)
  have hc : (0 : ℝ) < 1 / (c + 1) := by positivity
  filter_upwards [h.def hc] with L hL
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  have hLk : (0 : ℝ) ≤ (L : ℝ) ^ k := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLk, abs_of_nonneg (le_of_lt h2)] at hL
  have hcnn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
  have hlt : (c : ℝ) * (L : ℝ) ^ k < 2 ^ L := by
    have hmul : (c : ℝ) * (L : ℝ) ^ k ≤ (c : ℝ) * (1 / (c + 1) * 2 ^ L) :=
      mul_le_mul_of_nonneg_left hL hcnn
    have hfrac : (c : ℝ) * (1 / (c + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    nlinarith
  have : ((c * L ^ k : ℕ) : ℝ) < ((2 ^ L : ℕ) : ℝ) := by push_cast; exact hlt
  exact_mod_cast this

/-- **The flagship no-go for regime (c).**  For every polynomial bound `c · (log₂ N)^k` there
exist balanced semiprimes `N = p·q` (with `p < q < 2p`, so `p ≈ √N`) such that *every*
revealing pair for the successor iteration occurs after time exceeding that bound.  Hence no
`poly(log N)` number of steps of this `N`-explicit iteration can ever exhibit a factor. -/
theorem successor_reveal_superpolynomial (c k : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ 2 * p ∧
      ∀ (x0 : ℤ) (s t : ℕ), s < t →
        RevealsFactor (p * q) (polyOrbit (X + 1) x0 t - polyOrbit (X + 1) x0 s) →
        c * (Nat.log 2 (p * q)) ^ k < t := by
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp (eventually_poly_lt_two_pow (c * 4 ^ k) k)
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (2 ^ (L₀ + 1))
  obtain ⟨q, hq, hpq, hbal⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.pos.ne'
  refine ⟨p, q, hp, hq, hpq, hbal, ?_⟩
  intro x0 s t hst hrev
  set L : ℕ := Nat.log 2 p with hLdef
  -- `L ≥ L₀ + 1 ≥ 1`
  have hLbig : L₀ + 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) hple
  have hL1 : 1 ≤ L := by omega
  -- `2 ^ L ≤ p < 2 ^ (L+1)`
  have hp2 : 2 ^ L ≤ p := Nat.pow_log_le_self 2 hp.pos.ne'
  have hp3 : p < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
  -- `N = p * q < 2 ^ (2L+3)`
  have hN : p * q < 2 ^ (2 * L + 3) := by
    calc p * q ≤ p * (2 * p) := Nat.mul_le_mul_left p hbal
      _ = 2 * (p * p) := by ring
      _ < 2 * (2 ^ (L + 1) * 2 ^ (L + 1)) := by
          have := Nat.mul_lt_mul_of_lt_of_le hp3 (le_of_lt hp3) (Nat.zero_lt_of_lt hp3)
          omega
      _ = 2 ^ (2 * L + 3) := by ring
  have hlogN : Nat.log 2 (p * q) ≤ 2 * L + 2 := by
    have := Nat.log_lt_of_lt_pow (b := 2) (Nat.mul_pos hp.pos hq.pos).ne' hN
    omega
  -- polynomial in `log N` is dominated by `2 ^ L ≤ p`
  have hpoly : c * (Nat.log 2 (p * q)) ^ k ≤ c * (4 ^ k * L ^ k) := by
    have h1 : Nat.log 2 (p * q) ≤ 4 * L := by omega
    have h2 : (Nat.log 2 (p * q)) ^ k ≤ (4 * L) ^ k := Nat.pow_le_pow_left h1 k
    calc c * (Nat.log 2 (p * q)) ^ k ≤ c * (4 * L) ^ k := Nat.mul_le_mul_left c h2
      _ = c * (4 ^ k * L ^ k) := by rw [Nat.mul_pow]
  have hkey : c * 4 ^ k * L ^ k < 2 ^ L := hL₀ L (by omega)
  have hlt : c * (Nat.log 2 (p * q)) ^ k < p := by
    calc c * (Nat.log 2 (p * q)) ^ k ≤ c * (4 ^ k * L ^ k) := hpoly
      _ = c * 4 ^ k * L ^ k := by ring
      _ < 2 ^ L := hkey
      _ ≤ p := hp2
  -- and a reveal costs at least `min p q = p` steps
  have hne : p ≠ q := Nat.ne_of_lt hpq
  have hlb := successor_reveal_lower_bound hp hq hne x0 s t hst hrev
  have hmin : min p q = p := min_eq_left (le_of_lt hpq)
  rw [hmin] at hlb
  omega

/-! ## Regime (b): Pollard `p-1`, smoothness-dependent maps -/

/-- **Pollard `p-1` reveal criterion.**  `gcd (a^M - 1) N` is a nontrivial factor of
`N = p q` iff exactly one of the two multiplicative orders of `a` divides `M`. -/
theorem pollard_pm1_reveal_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a : ℤ) (M : ℕ) :
    RevealsFactor (p * q) (a ^ M - 1) ↔
      Xor' (orderOf ((a : ZMod p)) ∣ M) (orderOf ((a : ZMod q)) ∣ M) := by
  have hdvd : ∀ r : ℕ, ((r : ℤ) ∣ a ^ M - 1) ↔ orderOf ((a : ZMod r)) ∣ M := by
    intro r
    rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ M - 1) r]
    push_cast
    exact sub_eq_zero
  rw [crt_reveal_iff hp hq hne, hdvd p, hdvd q]

/-- **Regime (b) lower bound.**  A Pollard `p-1` reveal at exponent `M > 0` forces `M` to be at
least the smaller of the two multiplicative orders: the cost is the (unknown, `N`-invisible)
smoothness of `ord_p(a)`. -/
theorem pollard_pm1_lower_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a : ℤ) (M : ℕ) (hM : 0 < M) (hrev : RevealsFactor (p * q) (a ^ M - 1)) :
    min (orderOf ((a : ZMod p))) (orderOf ((a : ZMod q))) ≤ M := by
  rcases (pollard_pm1_reveal_iff hp hq hne a M).mp hrev with ⟨h, -⟩ | ⟨h, -⟩
  · exact le_trans (min_le_left _ _) (Nat.le_of_dvd hM h)
  · exact le_trans (min_le_right _ _) (Nat.le_of_dvd hM h)

/-! ## Barrier 6: the CRT idempotents are the factors -/

/-- **Circularity.**  A nontrivial idempotent mod `N` (equivalently, a CRT splitting of
`ZMod N`) immediately yields a nontrivial factor of `N`.  Hence any procedure that separates
the two CRT components must already know the factorisation. -/
theorem idempotent_reveals {N : ℕ} (hN : 1 < N) (e : ℤ) (hidem : (N : ℤ) ∣ e * (e - 1))
    (h0 : ¬ (N : ℤ) ∣ e) (h1 : ¬ (N : ℤ) ∣ e - 1) : 1 < Int.gcd e (N : ℤ) ∧ Int.gcd e N < N := by
  set g : ℕ := Int.gcd e (N : ℤ) with hg
  have hgN : g ∣ N := Int.ofNat_dvd.mp (by simpa using Int.gcd_dvd_right e (N : ℤ))
  have hgle : g ≤ N := Nat.le_of_dvd (by omega) hgN
  constructor
  · rcases Nat.lt_or_ge 1 g with h | h
    · exact h
    · -- `g ≤ 1`, so `g = 1` and `N` is coprime to `e`, forcing `N ∣ e - 1`
      exfalso
      interval_cases g
      · -- `g = 0` forces `N = 0`
        have : (N : ℤ) = 0 := by
          have := Int.gcd_eq_zero_iff.mp hg.symm
          exact_mod_cast this.2
        simp at this
        omega
      · have hcop : IsCoprime (N : ℤ) e := by
          rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
          exact hg.symm
        exact h1 (hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hidem))
  · rcases lt_or_eq_of_le hgle with h | h
    · exact h
    · exact absurd (h ▸ (Int.natCast_dvd_natCast.mpr (dvd_refl g)).trans
        (Int.gcd_dvd_left e (N : ℤ))) h0

/-! ## Regime (a): the verified CTST demo, `N = 341371 = 631 · 541`, `f(x) = x² + 1` -/

/-- The mod-`N` trace of the Pollard rho iteration `x ↦ x² + 1` from the seed `2`. -/
-- [dropped: platform already declares rhoTrace]
lemma dvd_polyOrbit_sub_rhoTrace (N : ℕ) (n : ℕ) :
    (N : ℤ) ∣ polyOrbit (X ^ 2 + 1) 2 n - (rhoTrace N n : ℤ) := by
  induction n with
  | zero => simp [polyOrbit, rhoTrace]
  | succ n ih =>
      rw [polyOrbit_succ]
      have hev : (X ^ 2 + 1 : ℤ[X]).eval (polyOrbit (X ^ 2 + 1) 2 n)
          = (polyOrbit (X ^ 2 + 1) 2 n) ^ 2 + 1 := by simp
      rw [hev]
      have hstep : ((rhoTrace N (n + 1) : ℕ) : ℤ) = ((rhoTrace N n : ℤ) ^ 2 + 1) % (N : ℤ) := by
        show ((((rhoTrace N n ^ 2 + 1) % N : ℕ)) : ℤ) = _
        push_cast [Int.natCast_mod]
        ring_nf
      rw [hstep]
      have h1 : (N : ℤ) ∣ ((rhoTrace N n : ℤ) ^ 2 + 1) - ((rhoTrace N n : ℤ) ^ 2 + 1) % (N : ℤ) :=
        ⟨((rhoTrace N n : ℤ) ^ 2 + 1) / (N : ℤ), by rw [Int.emod_def]; ring⟩
      have h2 : (N : ℤ) ∣ (polyOrbit (X ^ 2 + 1) 2 n) ^ 2 - (rhoTrace N n : ℤ) ^ 2 := by
        obtain ⟨c, hc⟩ := ih
        exact ⟨c * (polyOrbit (X ^ 2 + 1) 2 n + (rhoTrace N n : ℤ)), by
          have : polyOrbit (X ^ 2 + 1) 2 n = (rhoTrace N n : ℤ) + (N : ℤ) * c := by linarith
          rw [this]; ring⟩
      have := dvd_add h2 h1
      convert this using 1
      ring

set_option maxRecDepth 20000 in
lemma rhoTrace_23 : rhoTrace 341371 23 = 235156 := by rfl

set_option maxRecDepth 20000 in
lemma rhoTrace_36 : rhoTrace 341371 36 = 26926 := by rfl

/-- **CTST demo, the gcd.**  For `N = 341371 = 631·541`, `f(x) = x²+1`, seed `2`, the pair
`(s,t) = (23,36)` reveals the factor `631`. -/
theorem crt_demo_gcd :
    Int.gcd (polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23) ((341371 : ℕ) : ℤ) = 631 := by
  have h36 := dvd_polyOrbit_sub_rhoTrace 341371 36
  have h23 := dvd_polyOrbit_sub_rhoTrace 341371 23
  rw [rhoTrace_36] at h36
  rw [rhoTrace_23] at h23
  have hdvd : ((341371 : ℕ) : ℤ) ∣
      (polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23) - ((26926 : ℤ) - 235156) := by
    have := dvd_sub h36 h23
    convert this using 1
    ring
  rw [gcd_eq_of_dvd_sub hdvd]
  decide

/-- **CTST demo, the CRT split.**  The revealing difference is divisible by `631` and *not* by
`541` — an exclusive CRT collision, exactly as Fact 1 predicts. -/
theorem crt_demo_xor :
    Xor' ((631 : ℤ) ∣ (polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23))
         ((541 : ℤ) ∣ (polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23)) := by
  have hp : Nat.Prime 631 := by norm_num
  have hq : Nat.Prime 541 := by norm_num
  have hNe : (631 : ℕ) * 541 = 341371 := by norm_num
  have hrev : RevealsFactor (631 * 541)
      (polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23) := by
    unfold RevealsFactor
    rw [hNe, crt_demo_gcd]
    norm_num
  simpa using (crt_reveal_iff hp hq (by norm_num) _).mp hrev

/-- **CTST demo, the mechanism.**  The reveal at `(23,36)` *is* the closure of the mod-`631`
cycle, exclusive-or that of the mod-`541` cycle: the factor appears precisely at a one-sided
cycle closure of the reduced dynamics. -/
theorem crt_demo_closure :
    Xor' (modOrbit (X ^ 2 + 1) 631 2 36 = modOrbit (X ^ 2 + 1) 631 2 23)
         (modOrbit (X ^ 2 + 1) 541 2 36 = modOrbit (X ^ 2 + 1) 541 2 23) := by
  have hp : Nat.Prime 631 := by norm_num
  have hq : Nat.Prime 541 := by norm_num
  have hNe : (631 : ℕ) * 541 = 341371 := by norm_num
  have hrev : RevealsFactor (631 * 541)
      (polyOrbit (X ^ 2 + 1) 2 36 - polyOrbit (X ^ 2 + 1) 2 23) := by
    unfold RevealsFactor
    rw [hNe, crt_demo_gcd]
    norm_num
  exact (reveal_iff_xor_closure hp hq (by norm_num) (X ^ 2 + 1) 2 23 36).mp hrev

end CRTSplitNoGo
section
open CRTSplitNoGo
open Polynomial

theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (x0 : ℤ) (s t : ℕ) (hst : s < t)
    (hrev : RevealsFactor (p * q) (polyOrbit (X + 1) x0 t - polyOrbit (X + 1) x0 s)) :
    min p q ≤ t - s := by
  first
  | exact CRTSplitNoGo.successor_reveal_lower_bound hp hq hne x0 s t hst hrev
  | exact CRTSplitNoGo.successor_reveal_lower_bound
  | exact @CRTSplitNoGo.successor_reveal_lower_bound p q hp hq hne x0 s t hst hrev
  | apply CRTSplitNoGo.successor_reveal_lower_bound
  | exact CRTSplitNoGo.successor_reveal_lower_bound ..


end
