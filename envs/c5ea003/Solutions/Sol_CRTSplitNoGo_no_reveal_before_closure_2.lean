-- Prove2me | solution 2 for CRTSplitNoGo.no_reveal_before_closure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:49:11.132414+00:00
-- url     : https://prove2.me/submissions/223fec55-a71f-4730-87f5-d605a76a1074

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
open CRTSplitNoGo Polynomial in
theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (f : ℤ[X]) (x0 : ℤ) (T : ℕ)
    (hpinj : ∀ s t, s < t → t ≤ T → modOrbit f p x0 t ≠ modOrbit f p x0 s)
    (hqinj : ∀ s t, s < t → t ≤ T → modOrbit f q x0 t ≠ modOrbit f q x0 s) :
    ∀ s t, s < t → t ≤ T → ¬ RevealsFactor (p * q) (polyOrbit f x0 t - polyOrbit f x0 s) := by
  -- reduction commutes with iterating the polynomial map
  have hA : ∀ (m n : ℕ), ((polyOrbit f x0 n : ℤ) : ZMod m) = modOrbit f m x0 n := by
    intro m n
    induction n with
    | zero => simp [polyOrbit, modOrbit]
    | succ n ih =>
      simp only [polyOrbit, modOrbit, Function.iterate_succ_apply'] at ih ⊢
      rw [← ih, Polynomial.eval_intCast_map]
      simp
  -- a collision mod `m` is divisibility of the orbit difference
  have hB : ∀ (m s t : ℕ), modOrbit f m x0 t = modOrbit f m x0 s ↔
      (m : ℤ) ∣ polyOrbit f x0 t - polyOrbit f x0 s := by
    intro m s t
    rw [← hA, ← hA, ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]
  -- for distinct primes, `1 < gcd(d, pq) < pq` iff exactly one of `p, q` divides `d`
  have hC : ∀ d : ℤ, RevealsFactor (p * q) d ↔ Xor' ((p : ℤ) ∣ d) ((q : ℤ) ∣ d) := by
    intro d
    unfold RevealsFactor
    set g := Int.gcd d ((p * q : ℕ) : ℤ) with hg
    have hgd : g = Nat.gcd d.natAbs (p * q) := by
      rw [hg]
      rfl
    have hpg : p ∣ g ↔ (p : ℤ) ∣ d := by
      rw [hgd, Nat.dvd_gcd_iff, Int.natCast_dvd]
      exact ⟨fun h => h.1, fun h => ⟨h, dvd_mul_right p q⟩⟩
    have hqg : q ∣ g ↔ (q : ℤ) ∣ d := by
      rw [hgd, Nat.dvd_gcd_iff, Int.natCast_dvd]
      exact ⟨fun h => h.1, fun h => ⟨h, dvd_mul_left q p⟩⟩
    have hgpq : g ∣ p * q := by rw [hgd]; exact Nat.gcd_dvd_right _ _
    have hp1 := hp.one_lt
    have hq1 := hq.one_lt
    have hqp : ¬ q ∣ p := fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
    have hpq : ¬ p ∣ q := fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp hgpq
    have hy' := hp.eq_one_or_self_of_dvd y hy
    have hz' := hq.eq_one_or_self_of_dvd z hz
    rw [← hpg, ← hqg]
    rcases hy' with hy1 | hy1 <;> rcases hz' with hz1 | hz1 <;> rw [hy1, hz1] at hyz <;>
      rw [← hyz]
    · -- `g = 1`
      rw [one_mul]
      constructor
      · rintro ⟨h, -⟩
        exact absurd h (lt_irrefl 1)
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact absurd (Nat.le_of_dvd one_pos h) (by omega)
        · exact absurd (Nat.le_of_dvd one_pos h) (by omega)
    · -- `g = q`
      rw [one_mul]
      constructor
      · intro _
        exact Or.inr ⟨dvd_refl q, hpq⟩
      · intro _
        exact ⟨hq1, by nlinarith⟩
    · -- `g = p`
      rw [mul_one]
      constructor
      · intro _
        exact Or.inl ⟨dvd_refl p, hqp⟩
      · intro _
        exact ⟨hp1, by nlinarith⟩
    · -- `g = pq`
      constructor
      · rintro ⟨-, h⟩
        exact absurd h (lt_irrefl _)
      · rintro (⟨-, h⟩ | ⟨-, h⟩)
        · exact absurd (dvd_mul_left q p) h
        · exact absurd (dvd_mul_right p q) h
  have hkey : ∀ s t : ℕ, RevealsFactor (p * q) (polyOrbit f x0 t - polyOrbit f x0 s) ↔
      Xor' (modOrbit f p x0 t = modOrbit f p x0 s) (modOrbit f q x0 t = modOrbit f q x0 s) := by
    intro s t
    rw [hC, hB, hB]
  -- before either orbit closes, neither prime divides the difference
  intro s t hst htT h
  rw [hkey] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hpinj s t hst htT h1
  · exact hqinj s t hst htT h1
