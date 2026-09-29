-- Prove2me | solution 1 for CRTSplitNoGo.slpOrbit_crt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:03:36.514137+00:00
-- url     : https://prove2.me/submissions/990ee871-5ffa-46a6-8787-9d1c842d36de

-- Sol generated from Bridges/CRTSplitNoGoStraightLine.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoStraightLine

/-!
# The CRT-Split No-Go, Part X: the straight-line rigidity dichotomy

Parts I–II proved Fact 2 for *polynomial* maps.  Conjecture A of the previous cycle asked for
the general form: let `F` be any function computed by a straight-line program over `ZMod N`
with the operations `+`, `−`, `×`, division, and constants read off `N`.  Then either `F` is
CRT-blind — the same program computes both reduced components, so no information about the
splitting `N = p q` is produced — or the program hits, at some intermediate node, a value that
is **not invertible mod `N`**, and such a value either vanishes or *is* a factorisation.

This file proves that dichotomy.

## The formalisation

`SLE` is the type of straight-line expressions in one variable: a variable node, integer
constants (the "digits of `N`" of the informal statement — any integers at all, so the theorem
is stronger), the ring operations, and an inversion node.  `SLE.eval` interprets an expression
in an arbitrary commutative ring, an inversion node being `Ring.inverse` (which returns `0` on
a non-unit).  `SLE.AllUnits e x` says that every inversion node of `e` is applied to a unit at
input `x`; `SLE.DivFree e` says there is no inversion node at all.

## Main results

* `SLE.eval_hom` — **CRT-blindness.**  If all inversions succeed, evaluation commutes with any
  ring homomorphism: `φ (eval e x) = eval e (φ x)`.  `SLE.eval_hom_of_divFree` is the
  division-free case, where no hypothesis is needed.
* `SLE.toPoly` / `SLE.eval_toPoly` — a division-free program is literally an integer
  polynomial, so every theorem of Parts I–V applies to it verbatim
  (`slp_reveal_iff_xor_closure`).
* `slpOrbit_crt` — the orbit of an `SLE`-iteration in `ZMod (p q)` maps, under the Chinese
  remainder isomorphism, to the pair of orbits of *the same* program in `ZMod p` and `ZMod q`.
  This is the exact sense in which an `N`-explicit map "does not split the CRT".
* `nonunit_reveals` — **the escape is a factorisation.**  A value of `ZMod N` that is neither
  zero nor a unit yields `RevealsFactor N`.
* `sle_dichotomy` — the two together: for every straight-line program and every input, either
  the computation is CRT-blind, or some intermediate value hands you a nontrivial factor of `N`
  (or is zero).  Escaping polynomiality by dividing therefore *presupposes* the factorisation:
  this is barrier 6 (circularity), now for arbitrary straight-line programs rather than for
  idempotents alone.
-/

open CRTSplitNoGo

/-! ## Straight-line expressions -/


open SLE






/-! ## Ring homomorphisms commute with successful straight-line computation -/

/-- A ring homomorphism commutes with `Ring.inverse` at units. -/
lemma map_inverse_of_isUnit {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {u : R}
    (hu : IsUnit u) : φ (Ring.inverse u) = Ring.inverse (φ u) := by
  have hfu : IsUnit (φ u) := hu.map φ
  have h1 : φ (Ring.inverse u) * φ u = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel u hu, map_one]
  have h2 : φ u * Ring.inverse (φ u) = 1 := Ring.mul_inverse_cancel _ hfu
  calc φ (Ring.inverse u) = φ (Ring.inverse u) * (φ u * Ring.inverse (φ u)) := by rw [h2, mul_one]
    _ = (φ (Ring.inverse u) * φ u) * Ring.inverse (φ u) := by ring
    _ = Ring.inverse (φ u) := by rw [h1, one_mul]

/-- **CRT-blindness of straight-line programs.**  If every inversion of the program succeeds at
the input `x`, then evaluation commutes with an arbitrary ring homomorphism: the reduced value
is computed by *the same* program applied to the reduced input.  A program built from `N` can
therefore not act differently in the two CRT components of `ZMod N`. -/
theorem eval_hom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    ∀ (e : SLE) (x : R), AllUnits e x → φ (eval e x) = eval e (φ x)
  | var, x, _ => rfl
  | const c, x, _ => by simp [eval]
  | add a b, x, h => by
      simp only [eval, map_add, eval_hom φ a x h.1, eval_hom φ b x h.2]
  | sub a b, x, h => by
      simp only [eval, map_sub, eval_hom φ a x h.1, eval_hom φ b x h.2]
  | mul a b, x, h => by
      simp only [eval, map_mul, eval_hom φ a x h.1, eval_hom φ b x h.2]
  | inv a, x, h => by
      simp only [eval]
      rw [map_inverse_of_isUnit φ h.2, eval_hom φ a x h.1]


/-! ## Division-free programs are exactly polynomials -/

open Polynomial




/-! ## Straight-line iteration -/



lemma slpOrbit_succ {R : Type*} [CommRing R] (e : SLE) (x0 : R) (n : ℕ) :
    slpOrbit e x0 (n + 1) = SLE.eval e (slpOrbit e x0 n) := by
  simp [slpOrbit, Function.iterate_succ_apply']



/-- Homomorphic images of a straight-line orbit are orbits of the *same* program, provided
every inversion along the way succeeds. -/
theorem slpOrbit_hom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (e : SLE) (x0 : R) :
    ∀ n : ℕ, (∀ k < n, SLE.AllUnits e (slpOrbit e x0 k)) →
      φ (slpOrbit e x0 n) = slpOrbit e (φ x0) n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      rw [slpOrbit_succ, slpOrbit_succ, eval_hom φ e _ (h n (by omega)),
        ih (fun k hk => h k (by omega))]


/-! ## The escape from polynomiality is a factorisation -/



/-! ## Instances of the dichotomy on the CTST demo modulus -/







open CRTSplitNoGo in
theorem solution{m₁ m₂ : ℕ} (h : Nat.Coprime m₁ m₂) (e : SLE) (x0 : ZMod (m₁ * m₂)) (n : ℕ)
    (hunits : ∀ k < n, SLE.AllUnits e (slpOrbit e x0 k)) :
    (ZMod.chineseRemainder h) (slpOrbit e x0 n)
      = (slpOrbit e ((ZMod.chineseRemainder h) x0).1 n,
         slpOrbit e ((ZMod.chineseRemainder h) x0).2 n) := by
  have h1 : (RingHom.fst (ZMod m₁) (ZMod m₂)).comp
      (ZMod.chineseRemainder h).toRingHom (slpOrbit e x0 n)
      = slpOrbit e (((ZMod.chineseRemainder h) x0).1) n :=
    slpOrbit_hom ((RingHom.fst (ZMod m₁) (ZMod m₂)).comp (ZMod.chineseRemainder h).toRingHom)
      e x0 n hunits
  have h2 : (RingHom.snd (ZMod m₁) (ZMod m₂)).comp
      (ZMod.chineseRemainder h).toRingHom (slpOrbit e x0 n)
      = slpOrbit e (((ZMod.chineseRemainder h) x0).2) n :=
    slpOrbit_hom ((RingHom.snd (ZMod m₁) (ZMod m₂)).comp (ZMod.chineseRemainder h).toRingHom)
      e x0 n hunits
  exact Prod.ext h1 h2
