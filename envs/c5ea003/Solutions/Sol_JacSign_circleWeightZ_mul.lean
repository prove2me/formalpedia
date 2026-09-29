-- Prove2me | solution 1 for JacSign.circleWeightZ_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:15:11.584985+00:00
-- url     : https://prove2.me/submissions/159012b5-b239-4bf7-b00b-f3029fab2a80

-- Sol generated from Tropical/JacobiSignedMultiplicative.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedMultiplicative
import Definitions.Def_Tropical_JacobiSignedWeilFloorBound

/-!
# Multiplicativity of the Jacobi-signed circle count and the semiprime Weil floor

The Jacobi-signed circle count is defined for an arbitrary modulus `n` by weighting the
circle `x² + y² = 1` over `ZMod n` with the *Jacobi symbol* `(x / n)`.  Summing the `y`'s
away, this is the character sum

`WZ n = ∑_{x : ZMod n} (x(1-x²) / n)`.

Main results.

* `JacSign.jchar_mul` : `x ↦ (x / n)` is multiplicative on `ZMod n`.
* `JacSign.WZ_mul` : `WZ (m n) = WZ m · WZ n` for coprime moduli — the Chinese remainder
  theorem turns the circle count into a **symmetric product over the factors**.
* `JacSign.WZ_prime` : for a prime modulus the Jacobi-signed count is the Legendre
  character sum `W p` of the core file.
* `JacSign.WZ_semiprime` : `WZ (p q) = W p · W q` for distinct primes.
* `JacSign.WZ_semiprime_sq_le` : `WZ (p q) ^ 2 ≤ 16 · p q`, i.e. `|WZ N| ≤ 4 √N`:
  **the semiprime Weil floor.**  The signal available to a factoring witness is
  `O(√N)` against a search space of size `N`.
* `JacSign.WZ_semiprime_eq_zero_of_three_mod_four` : if either prime is `≡ 3 (mod 4)`
  the whole statistic vanishes.
-/

open Finset

open JacSign




/-- Reducing the modulus: the Jacobi symbol only sees the residue class. -/
theorem jchar_cast {N k : ℕ} [NeZero N] [NeZero k] (x : ZMod N) (hd : k ∣ N) :
    jacobiSym (x.val : ℤ) k = jchar k (ZMod.castHom hd (ZMod k) x) := by
  apply jacobiSym.mod_left'
  have h : (((x.val : ℤ)) : ZMod k) = ((((ZMod.castHom hd (ZMod k) x).val : ℤ)) : ZMod k) := by
    push_cast
    simp [ZMod.natCast_val, ZMod.castHom_apply]
  exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h

/-- The Jacobi symbol splits along a coprime factorisation of the modulus. -/
theorem jchar_split (m n : ℕ) [NeZero m] [NeZero n] (x : ZMod (m * n)) :
    haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    jchar (m * n) x
      = jchar m (ZMod.castHom (dvd_mul_right m n) (ZMod m) x)
        * jchar n (ZMod.castHom (dvd_mul_left n m) (ZMod n) x) := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  show jacobiSym _ (m * n) = _
  rw [jacobiSym.mul_right, jchar_cast (k := m) x (dvd_mul_right m n),
    jchar_cast (k := n) x (dvd_mul_left n m)]






/-! ### The geometric statistic for a composite modulus -/








open JacSign in
theorem solution(m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    circleWeightZ (m * n) = circleWeightZ m * circleWeightZ n := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  set e := ZMod.chineseRemainder h with he
  set f : ZMod (m * n) →+* ZMod m := ZMod.castHom (dvd_mul_right m n) (ZMod m) with hf
  set g : ZMod (m * n) →+* ZMod n := ZMod.castHom (dvd_mul_left n m) (ZMod n) with hg
  have hef : ∀ x, (e x).1 = f x := by intro x; simp [he, hf, ZMod.chineseRemainder]
  have heg : ∀ x, (e x).2 = g x := by intro x; simp [he, hg, ZMod.chineseRemainder]
  set G : ZMod m × ZMod m → ℤ := fun z => if z.1 ^ 2 + z.2 ^ 2 = 1 then jchar m z.1 else 0 with hG
  set H : ZMod n × ZMod n → ℤ := fun z => if z.1 ^ 2 + z.2 ^ 2 = 1 then jchar n z.1 else 0 with hH
  have hcond : ∀ x y : ZMod (m * n),
      (x ^ 2 + y ^ 2 = 1) ↔ ((f x) ^ 2 + (f y) ^ 2 = 1 ∧ (g x) ^ 2 + (g y) ^ 2 = 1) := by
    intro x y
    constructor
    · intro hxy
      refine ⟨?_, ?_⟩
      · have := congrArg f hxy; simpa [map_add, map_pow] using this
      · have := congrArg g hxy; simpa [map_add, map_pow] using this
    · rintro ⟨h1, h2⟩
      refine e.injective (Prod.ext ?_ ?_)
      · simpa [hef, map_add, map_pow] using h1
      · simpa [heg, map_add, map_pow] using h2
  have hterm : ∀ z : ZMod (m * n) × ZMod (m * n),
      (if z.1 ^ 2 + z.2 ^ 2 = 1 then jchar (m * n) z.1 else 0)
        = G (f z.1, f z.2) * H (g z.1, g z.2) := by
    rintro ⟨x, y⟩
    simp only [hG, hH]
    by_cases hxy : x ^ 2 + y ^ 2 = 1
    · obtain ⟨h1, h2⟩ := (hcond x y).mp hxy
      rw [if_pos hxy, if_pos h1, if_pos h2, jchar_split m n x]
    · rw [if_neg hxy]
      rcases not_and_or.mp ((hcond x y).not.mp hxy) with h1 | h1
      · rw [if_neg h1, zero_mul]
      · rw [if_neg h1, mul_zero]
  have hdouble : circleWeightZ (m * n)
      = ∑ z : ZMod (m * n) × ZMod (m * n),
          (if z.1 ^ 2 + z.2 ^ 2 = 1 then jchar (m * n) z.1 else 0) := by
    rw [circleWeightZ]
    exact (Fintype.sum_prod_type (fun z : ZMod (m * n) × ZMod (m * n) =>
      if z.1 ^ 2 + z.2 ^ 2 = 1 then jchar (m * n) z.1 else 0)).symm
  have hEq : ∑ z : ZMod (m * n) × ZMod (m * n), G (f z.1, f z.2) * H (g z.1, g z.2)
      = ∑ w : (ZMod m × ZMod m) × (ZMod n × ZMod n), G w.1 * H w.2 := by
    refine Fintype.sum_equiv ((e.toEquiv.prodCongr e.toEquiv).trans
      (Equiv.prodProdProdComm (ZMod m) (ZMod n) (ZMod m) (ZMod n))) _ _ fun z => ?_
    have hz : ((e.toEquiv.prodCongr e.toEquiv).trans
        (Equiv.prodProdProdComm (ZMod m) (ZMod n) (ZMod m) (ZMod n))) z
        = ((f z.1, f z.2), (g z.1, g z.2)) := by
      simp only [Equiv.prodProdProdComm, Equiv.trans_apply, Equiv.prodCongr_apply,
        Equiv.coe_fn_mk, Prod.mk.injEq]
      exact ⟨⟨hef _, hef _⟩, heg _, heg _⟩
    rw [hz]
  have hGm : circleWeightZ m = ∑ a : ZMod m × ZMod m, G a := by
    rw [circleWeightZ, hG]
    exact (Fintype.sum_prod_type (fun z : ZMod m × ZMod m =>
      if z.1 ^ 2 + z.2 ^ 2 = 1 then jchar m z.1 else 0)).symm
  have hHn : circleWeightZ n = ∑ b : ZMod n × ZMod n, H b := by
    rw [circleWeightZ, hH]
    exact (Fintype.sum_prod_type (fun z : ZMod n × ZMod n =>
      if z.1 ^ 2 + z.2 ^ 2 = 1 then jchar n z.1 else 0)).symm
  rw [hdouble, Finset.sum_congr rfl fun z _ => hterm z, hEq, hGm, hHn,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
