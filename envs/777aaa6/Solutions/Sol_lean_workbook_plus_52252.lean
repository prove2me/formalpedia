-- Prove2me | solution 1 for lean_workbook_plus_52252
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:04:13.441633+00:00
-- url     : https://prove2.me/submissions/38b73a89-616d-452c-b353-d8a85dce9f63

import Mathlib

set_option autoImplicit false

noncomputable section

namespace PositiveRationalQuarterTurn

def naturalLift (g : ℕ → ℚ) (n : ℕ) : ℚ :=
  n.factorization.prod fun p k => g p ^ k

theorem naturalLift_pos (g : ℕ → ℚ) (hg : ∀ p, 0 < g p) (n : ℕ) :
    0 < naturalLift g n := by
  unfold naturalLift Finsupp.prod
  exact Finset.prod_pos fun p _ => pow_pos (hg p) _

theorem naturalLift_one (g : ℕ → ℚ) : naturalLift g 1 = 1 := by
  simp [naturalLift]

theorem naturalLift_prime (g : ℕ → ℚ) (p : ℕ) (hp : p.Prime) :
    naturalLift g p = g p := by
  simp [naturalLift, hp.factorization]

theorem naturalLift_mul (g : ℕ → ℚ) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    naturalLift g (m * n) = naturalLift g m * naturalLift g n := by
  unfold naturalLift
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index (by simp) (by intros; exact pow_add _ _ _)

def rationalLift (g : ℕ → ℚ) (q : ℚ) : ℚ :=
  naturalLift g q.num.natAbs / naturalLift g q.den

theorem rationalLift_pos (g : ℕ → ℚ) (hg : ∀ p, 0 < g p) (q : ℚ) :
    0 < rationalLift g q :=
  div_pos (naturalLift_pos g hg _) (naturalLift_pos g hg _)

theorem positive_ratio (q : ℚ) (hq : 0 < q) :
    (q.num.natAbs : ℚ) / q.den = q := by
  have h : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have hc : (q.num.natAbs : ℚ) = q.num := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) h
  rw [hc, Rat.num_div_den]

theorem numerator_pos (q : ℚ) (hq : 0 < q) : 0 < q.num.natAbs := by
  exact Int.natAbs_pos.mpr (Rat.num_pos.mpr hq).ne'

theorem rationalLift_ratio (g : ℕ → ℚ) (hg : ∀ p, 0 < g p)
    (q : ℚ) (hq : 0 < q) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (he : q = (m : ℚ) / n) :
    rationalLift g q = naturalLift g m / naturalLift g n := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : q.num.natAbs * n = m * q.den := by
    have h := (div_eq_div_iff hd hnq).mp ((positive_ratio q hq).trans he)
    exact_mod_cast h
  have hf := congrArg (naturalLift g) hc
  rw [naturalLift_mul g _ _ (numerator_pos q hq).ne' hn.ne',
    naturalLift_mul g _ _ hm.ne' q.den_pos.ne'] at hf
  exact (div_eq_div_iff (naturalLift_pos g hg _).ne'
    (naturalLift_pos g hg _).ne').mpr hf

theorem rationalLift_nat (g : ℕ → ℚ) (hg : ∀ p, 0 < g p)
    (n : ℕ) (hn : 0 < n) : rationalLift g n = naturalLift g n := by
  have h := rationalLift_ratio g hg n (by exact_mod_cast hn) n 1 hn (by omega) (by simp)
  simpa [naturalLift_one] using h

theorem rationalLift_one (g : ℕ → ℚ) (hg : ∀ p, 0 < g p) : rationalLift g 1 = 1 := by
  simpa [naturalLift_one] using rationalLift_nat g hg 1 (by omega)

theorem rationalLift_mul (g : ℕ → ℚ) (hg : ∀ p, 0 < g p)
    (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    rationalLift g (x * y) = rationalLift g x * rationalLift g y := by
  have he : x * y = ((x.num.natAbs * y.num.natAbs : ℕ) : ℚ) / (x.den * y.den : ℕ) := by
    push_cast
    rw [mul_div_mul_comm, positive_ratio x hx, positive_ratio y hy]
  rw [rationalLift_ratio g hg (x * y) (mul_pos hx hy) _ _
    (Nat.mul_pos (numerator_pos x hx) (numerator_pos y hy))
    (Nat.mul_pos x.den_pos y.den_pos) he,
    naturalLift_mul g _ _ (numerator_pos x hx).ne' (numerator_pos y hy).ne',
    naturalLift_mul g _ _ x.den_pos.ne' y.den_pos.ne']
  exact mul_div_mul_comm _ _ _ _

theorem rationalLift_inv (g : ℕ → ℚ) (hg : ∀ p, 0 < g p)
    (x : ℚ) (hx : 0 < x) : rationalLift g x⁻¹ = (rationalLift g x)⁻¹ := by
  have h := rationalLift_mul g hg x x⁻¹ hx (inv_pos.mpr hx)
  rw [mul_inv_cancel₀ hx.ne', rationalLift_one g hg] at h
  rw [← one_div (rationalLift g x)]
  apply (eq_div_iff (rationalLift_pos g hg x).ne').mpr
  simpa only [mul_comm] using h.symm

theorem rationalLift_div (g : ℕ → ℚ) (hg : ∀ p, 0 < g p)
    (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    rationalLift g (x / y) = rationalLift g x / rationalLift g y := by
  rw [div_eq_mul_inv, rationalLift_mul g hg x y⁻¹ hx (inv_pos.mpr hy),
    rationalLift_inv g hg y hy, div_eq_mul_inv]

noncomputable def primeEnumeration : (ℕ × Bool) ≃ Nat.Primes := by
  letI := Denumerable.ofEncodableOfInfinite (ℕ × Bool)
  letI := Encodable.ofCountable Nat.Primes
  letI := Denumerable.ofEncodableOfInfinite Nat.Primes
  exact Denumerable.equiv₂ _ _

def primeValue (e : (ℕ × Bool) ≃ Nat.Primes) (p : ℕ) : ℚ :=
  if hp : p.Prime then
    if (e.symm ⟨p, hp⟩).2 then
      ((e ((e.symm ⟨p, hp⟩).1, false) : ℕ) : ℚ)⁻¹
    else ((e ((e.symm ⟨p, hp⟩).1, true) : ℕ) : ℚ)
  else 1

theorem primeValue_pos (e : (ℕ × Bool) ≃ Nat.Primes) (p : ℕ) : 0 < primeValue e p := by
  unfold primeValue
  split_ifs with hp hb
  · apply inv_pos.mpr
    exact_mod_cast (e ((e.symm ⟨p, hp⟩).1, false)).property.pos
  · exact_mod_cast (e ((e.symm ⟨p, hp⟩).1, true)).property.pos
  · norm_num

theorem primeValue_left (e : (ℕ × Bool) ≃ Nat.Primes) (n : ℕ) :
    primeValue e (e (n, false)) = ((e (n, true) : ℕ) : ℚ) := by
  simp [primeValue, (e (n, false)).property]

theorem primeValue_right (e : (ℕ × Bool) ≃ Nat.Primes) (n : ℕ) :
    primeValue e (e (n, true)) = ((e (n, false) : ℕ) : ℚ)⁻¹ := by
  simp [primeValue, (e (n, true)).property]

def quarterTurn (e : (ℕ × Bool) ≃ Nat.Primes) : ℚ → ℚ := rationalLift (primeValue e)

theorem quarterTurn_pos (e : (ℕ × Bool) ≃ Nat.Primes) (x : ℚ) : 0 < quarterTurn e x :=
  rationalLift_pos _ (primeValue_pos e) x

theorem quarterTurn_one (e : (ℕ × Bool) ≃ Nat.Primes) : quarterTurn e 1 = 1 :=
  rationalLift_one _ (primeValue_pos e)

theorem quarterTurn_mul (e : (ℕ × Bool) ≃ Nat.Primes) (x y : ℚ)
    (hx : 0 < x) (hy : 0 < y) : quarterTurn e (x * y) = quarterTurn e x * quarterTurn e y :=
  rationalLift_mul _ (primeValue_pos e) x y hx hy

theorem quarterTurn_inv (e : (ℕ × Bool) ≃ Nat.Primes) (x : ℚ) (hx : 0 < x) :
    quarterTurn e x⁻¹ = (quarterTurn e x)⁻¹ :=
  rationalLift_inv _ (primeValue_pos e) x hx

theorem quarterTurn_div (e : (ℕ × Bool) ≃ Nat.Primes) (x y : ℚ)
    (hx : 0 < x) (hy : 0 < y) : quarterTurn e (x / y) = quarterTurn e x / quarterTurn e y :=
  rationalLift_div _ (primeValue_pos e) x y hx hy

theorem quarterTurn_prime (e : (ℕ × Bool) ≃ Nat.Primes) (p : Nat.Primes) :
    quarterTurn e (p : ℕ) = primeValue e p := by
  exact (rationalLift_nat _ (primeValue_pos e) p p.property.pos).trans
    (naturalLift_prime _ p p.property)

theorem quarterTurn_square_prime (e : (ℕ × Bool) ≃ Nat.Primes) (p : Nat.Primes) :
    quarterTurn e (quarterTurn e (p : ℕ)) = ((p : ℕ) : ℚ)⁻¹ := by
  obtain ⟨⟨n, b⟩, rfl⟩ := e.surjective p
  cases b
  · rw [quarterTurn_prime, primeValue_left, quarterTurn_prime, primeValue_right]
  · rw [quarterTurn_prime, primeValue_right,
      quarterTurn_inv e _ (by exact_mod_cast (e (n, false)).property.pos),
      quarterTurn_prime, primeValue_left]

theorem quarterTurn_square_nat (e : (ℕ × Bool) ≃ Nat.Primes) (n : ℕ) (hn : 0 < n) :
    quarterTurn e (quarterTurn e n) = (n : ℚ)⁻¹ := by
  have h : ∀ n : ℕ, 0 < n → quarterTurn e (quarterTurn e n) = (n : ℚ)⁻¹ := by
    apply Nat.recOnMul
    · omega
    · intro _
      simp [quarterTurn_one]
    · intro p hp _
      exact quarterTurn_square_prime e ⟨p, hp⟩
    · intro a b ha hb hab
      have hapos : 0 < a := Nat.pos_of_mul_pos_right hab
      have hbpos : 0 < b := Nat.pos_of_mul_pos_left hab
      have haq : (0 : ℚ) < a := by exact_mod_cast hapos
      have hbq : (0 : ℚ) < b := by exact_mod_cast hbpos
      rw [Nat.cast_mul, quarterTurn_mul e _ _ haq hbq,
        quarterTurn_mul e _ _ (quarterTurn_pos e _) (quarterTurn_pos e _),
        ha hapos, hb hbpos, mul_inv_rev]
      ring
  exact h n hn

theorem quarterTurn_square (e : (ℕ × Bool) ≃ Nat.Primes) (x : ℚ) (hx : 0 < x) :
    quarterTurn e (quarterTurn e x) = x⁻¹ := by
  have hn : (0 : ℚ) < x.num.natAbs := by exact_mod_cast numerator_pos x hx
  have hd : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have hr := positive_ratio x hx
  calc
    quarterTurn e (quarterTurn e x) =
        quarterTurn e (quarterTurn e (x.num.natAbs : ℚ) / quarterTurn e (x.den : ℚ)) := by
      congr 1
      rw [← quarterTurn_div e _ _ hn hd, hr]
    _ = quarterTurn e (quarterTurn e (x.num.natAbs : ℚ)) /
        quarterTurn e (quarterTurn e (x.den : ℚ)) :=
      quarterTurn_div e _ _ (quarterTurn_pos e _) (quarterTurn_pos e _)
    _ = (x.num.natAbs : ℚ)⁻¹ / (x.den : ℚ)⁻¹ := by
      rw [quarterTurn_square_nat e _ (numerator_pos x hx),
        quarterTurn_square_nat e _ x.den_pos]
    _ = ((x.num.natAbs : ℚ) / (x.den : ℚ))⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm]
    _ = x⁻¹ := congrArg Inv.inv hr

theorem quarterTurn_source (e : (ℕ × Bool) ≃ Nat.Primes) (x y : ℚ)
    (hx : 0 < x) (hy : 0 < y) : quarterTurn e (x * quarterTurn e y) = quarterTurn e x / y := by
  rw [quarterTurn_mul e _ _ hx (quarterTurn_pos e _), quarterTurn_square e y hy,
    div_eq_mul_inv]

theorem source_exists : ∃ f : ℚ → ℚ, (∀ x, 0 < x → 0 < f x) ∧
    ∀ x y, 0 < x → 0 < y → f (x * f y) = f x / y :=
  ⟨quarterTurn primeEnumeration, fun x _ => quarterTurn_pos _ x, quarterTurn_source _⟩

def SourceEquation (f : ℚ → ℚ) : Prop :=
  ∀ x y, 0 < x → 0 < y → f (x * f y) = f x / y

theorem source_one (f : ℚ → ℚ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hf : SourceEquation f) : f 1 = 1 := by
  have hc : f (f 1) = f 1 := by simpa using hf 1 1 (by norm_num) (by norm_num)
  have h := hf 1 (f 1) (by norm_num) (hpos 1 (by norm_num))
  simpa only [one_mul, hc, div_self (hpos 1 (by norm_num)).ne'] using h

theorem source_square (f : ℚ → ℚ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hf : SourceEquation f) (x : ℚ) (hx : 0 < x) : f (f x) = x⁻¹ := by
  simpa [source_one f hpos hf] using hf 1 x (by norm_num) hx

theorem source_inverse (f : ℚ → ℚ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hf : SourceEquation f) (x : ℚ) (hx : 0 < x) : f x⁻¹ = (f x)⁻¹ := by
  have h := source_square f hpos hf (f x) (hpos x hx)
  rwa [source_square f hpos hf x hx] at h

theorem source_multiplicative (f : ℚ → ℚ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hf : SourceEquation f) (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    f (x * y) = f x * f y := by
  have h := hf x (f y⁻¹) hx (hpos y⁻¹ (inv_pos.mpr hy))
  rw [source_square f hpos hf y⁻¹ (inv_pos.mpr hy), inv_inv,
    source_inverse f hpos hf y hy, div_inv_eq_mul] at h
  exact h

theorem source_iff (f : ℚ → ℚ) (hpos : ∀ x, 0 < x → 0 < f x) :
    SourceEquation f ↔
      (∀ x y, 0 < x → 0 < y → f (x * y) = f x * f y) ∧
      (∀ x, 0 < x → f (f x) = x⁻¹) := by
  constructor
  · intro hf
    exact ⟨source_multiplicative f hpos hf, source_square f hpos hf⟩
  · rintro ⟨hm, hs⟩ x y hx hy
    rw [hm x (f y) hx (hpos y hy), hs y hy, div_eq_mul_inv]

theorem source_bijective (f : ℚ → ℚ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hf : SourceEquation f) : Set.BijOn f (Set.Ioi 0) (Set.Ioi 0) := by
  refine ⟨fun x hx => hpos x hx, ?_, ?_⟩
  · intro x hx y hy he
    have h := congrArg f he
    rw [source_square f hpos hf x hx, source_square f hpos hf y hy] at h
    exact inv_injective h
  · intro y hy
    refine ⟨f y⁻¹, hpos _ (inv_pos.mpr hy), ?_⟩
    rw [source_square f hpos hf y⁻¹ (inv_pos.mpr hy), inv_inv]

theorem source_fourth_iterate (f : ℚ → ℚ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hf : SourceEquation f) (x : ℚ) (hx : 0 < x) : f (f (f (f x))) = x := by
  rw [source_square f hpos hf (f (f x)) (hpos _ (hpos x hx)),
    source_square f hpos hf x hx, inv_inv]

theorem source_fixed_iff (f : ℚ → ℚ) (hpos : ∀ x, 0 < x → 0 < f x)
    (hf : SourceEquation f) (x : ℚ) (hx : 0 < x) : f x = x ↔ x = 1 := by
  constructor
  · intro he
    have h := source_square f hpos hf x hx
    rw [he, he] at h
    have hs : x * x = 1 := by
      calc
        x * x = x⁻¹ * x := congrArg (fun z => z * x) h
        _ = 1 := inv_mul_cancel₀ hx.ne'
    nlinarith
  · rintro rfl
    exact source_one f hpos hf

theorem positive_domain_congruence (f g : ℚ → ℚ)
    (hpos : ∀ x, 0 < x → 0 < f x) (he : Set.EqOn g f (Set.Ioi 0))
    (hf : SourceEquation f) : (∀ x, 0 < x → 0 < g x) ∧ SourceEquation g := by
  have hgpos : ∀ x, 0 < x → 0 < g x := by
    intro x hx
    rw [he hx]
    exact hpos x hx
  refine ⟨hgpos, ?_⟩
  intro x y hx hy
  rw [he (mul_pos hx (hgpos y hy)), he hy, he hx]
  exact hf x y hx hy

end PositiveRationalQuarterTurn

theorem solution : ∃ f : ℚ → ℚ, ∀ x y : ℚ, 0 < x ∧ 0 < y → f (x * f y) = f x / y := by
  obtain ⟨f, _, hf⟩ := PositiveRationalQuarterTurn.source_exists
  exact ⟨f, fun x y h => hf x y h.1 h.2⟩

#print axioms PositiveRationalQuarterTurn.naturalLift
#print axioms PositiveRationalQuarterTurn.naturalLift_pos
#print axioms PositiveRationalQuarterTurn.naturalLift_one
#print axioms PositiveRationalQuarterTurn.naturalLift_prime
#print axioms PositiveRationalQuarterTurn.naturalLift_mul
#print axioms PositiveRationalQuarterTurn.rationalLift
#print axioms PositiveRationalQuarterTurn.rationalLift_pos
#print axioms PositiveRationalQuarterTurn.positive_ratio
#print axioms PositiveRationalQuarterTurn.numerator_pos
#print axioms PositiveRationalQuarterTurn.rationalLift_ratio
#print axioms PositiveRationalQuarterTurn.rationalLift_nat
#print axioms PositiveRationalQuarterTurn.rationalLift_one
#print axioms PositiveRationalQuarterTurn.rationalLift_mul
#print axioms PositiveRationalQuarterTurn.rationalLift_inv
#print axioms PositiveRationalQuarterTurn.rationalLift_div
#print axioms PositiveRationalQuarterTurn.primeEnumeration
#print axioms PositiveRationalQuarterTurn.primeValue
#print axioms PositiveRationalQuarterTurn.primeValue_pos
#print axioms PositiveRationalQuarterTurn.primeValue_left
#print axioms PositiveRationalQuarterTurn.primeValue_right
#print axioms PositiveRationalQuarterTurn.quarterTurn
#print axioms PositiveRationalQuarterTurn.quarterTurn_pos
#print axioms PositiveRationalQuarterTurn.quarterTurn_one
#print axioms PositiveRationalQuarterTurn.quarterTurn_mul
#print axioms PositiveRationalQuarterTurn.quarterTurn_inv
#print axioms PositiveRationalQuarterTurn.quarterTurn_div
#print axioms PositiveRationalQuarterTurn.quarterTurn_prime
#print axioms PositiveRationalQuarterTurn.quarterTurn_square_prime
#print axioms PositiveRationalQuarterTurn.quarterTurn_square_nat
#print axioms PositiveRationalQuarterTurn.quarterTurn_square
#print axioms PositiveRationalQuarterTurn.quarterTurn_source
#print axioms PositiveRationalQuarterTurn.source_exists
#print axioms PositiveRationalQuarterTurn.SourceEquation
#print axioms PositiveRationalQuarterTurn.source_one
#print axioms PositiveRationalQuarterTurn.source_square
#print axioms PositiveRationalQuarterTurn.source_inverse
#print axioms PositiveRationalQuarterTurn.source_multiplicative
#print axioms PositiveRationalQuarterTurn.source_iff
#print axioms PositiveRationalQuarterTurn.source_bijective
#print axioms PositiveRationalQuarterTurn.source_fourth_iterate
#print axioms PositiveRationalQuarterTurn.source_fixed_iff
#print axioms PositiveRationalQuarterTurn.positive_domain_congruence
#print axioms solution
