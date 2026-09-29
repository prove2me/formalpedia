-- Prove2me | solution 1 for SuperspecialK3Symplectic.nonSymplecticIndex_not_dvd_char
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:52:31.070147+00:00
-- url     : https://prove2.me/submissions/3549730a-68c3-44ed-9c7d-72a63f316103

-- Sol generated from Novelty/SuperspecialK3Symplectic.lean
import Mathlib
import Definitions.Def_Novelty_SuperspecialK3Symplectic
/-
# The symplectic / non-symplectic dichotomy for finite automorphism groups (K3 model)

This file formalizes the **group-theoretic skeleton** underlying the conjecture of Ohashi–Schütt
type that, for the superspecial K3 surface `X` over an algebraically closed field of characteristic
`p > 11`, a finite automorphism group `G ≤ Aut(X)` whose symplectic part `G_s` is *maximal* (a Mukai
group) admits **no non-trivial non-symplectic extension**, i.e. the non-symplectic index `[G : G_s]`
equals `1`.

The geometry that defines the dichotomy is the action of `G` on the one–dimensional space of global
regular `2`-forms `H⁰(X, Ω²_X) ≅ k`.  This action is recorded by the **period character**
`χ : G →* kˣ`.  Its kernel is the **symplectic subgroup** `G_s` (automorphisms acting trivially on
the `2`-form), and the quotient `G / G_s ≅ im χ` is the **non-symplectic part**, whose order is the
non-symplectic index `n = [G : G_s]`.

We isolate the parts of the statement that are *intrinsic group theory / characteristic-`p` algebra*,
independent of any K3-specific input:

* `nonSymplectic_isCyclic` — the non-symplectic part `im χ` is **cyclic** (a finite subgroup of the
  units of a field).  This is the structural reason the non-symplectic part is a single cyclic group
  `C_n`, exactly as in the geometric classification.
* `nonSymplecticIndex_eq_card_range` and `card_eq_symplectic_mul_index` — the bookkeeping identities
  `[G : G_s] = #(im χ)` and `#G = #G_s · [G : G_s]`.
* `noNonTrivialExtension_iff` — the precise meaning of the conjecture's conclusion:
  `G = G_s ↔ [G : G_s] = 1 ↔ χ` is trivial.
* `nonSymplecticIndex_not_dvd_char` — a genuine **characteristic-`p` obstruction**: the non-symplectic
  index `n` is **never divisible by `p`** (a finite subgroup of `kˣ` has order prime to `char k`,
  because `kˣ` has no non-trivial `p`-torsion in characteristic `p`).  This is the "tameness" of the
  non-symplectic part that is built into the `p > 11` hypothesis.

The deep geometric input — that maximality of `G_s` forces `n = 1` — is *not* provided by Mathlib and
is recorded as a hypothesis / future direction; here we prove everything that the group theory and the
field arithmetic give unconditionally.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the conjecture's conclusion "`[G:G_s] = 1`" should decompose into (a) a
purely structural fact that the non-symplectic part is a *cyclic* group `C_n` realized inside `kˣ`,
and (b) an arithmetic constraint forcing `n = 1`.  Bolder: part of the `n=1` phenomenon should already
be visible as a *characteristic-`p` tameness* statement that the non-symplectic order is automatically
prime to `p`, independent of K3 geometry.

Experiment (Experimenter): model the period action as a character `χ : G →* kˣ`.  Mathlib gives
`Subgroup.index_ker : χ.ker.index = Nat.card χ.range` and the cyclicity of finite subgroups of `kˣ`
(`subgroup_units_cyclic`).  The characteristic-`p` obstruction is proved by Cauchy's theorem: if
`p ∣ #(im χ)` there would be a unit of order `p`, but in characteristic `p`, `xᵖ = 1 ⇒ (x-1)ᵖ = 0 ⇒
x = 1` via `sub_pow_char`.

Analysis (Analyst): the cyclic structure and the bookkeeping identities are unconditional and faithful.
The characteristic-`p` obstruction is the honest, provable shadow of the geometric tameness: it shows
the *non-symplectic* order is prime to `p` for free; the missing geometric input only concerns the
*symplectic* order (the Mukai group) and the rigidity that pins `n` to `1`.

Critique (Critic): is `noNonTrivialExtension_iff` trivial?  No — it threads the kernel/index/range
dictionary and the field-units cyclicity.  Is `nonSymplecticIndex_not_dvd_char` vacuous?  No — it
produces a genuine contradiction from a hypothetical order-`p` unit via `sub_pow_char`.  Hidden
assumptions: `Finite G` (automorphism groups of K3 are finite) and `Field k` of characteristic `p`;
both faithful to the superspecial K3 setting.

Synthesis (PI): the symplectic/non-symplectic dichotomy is captured exactly — non-symplectic part is
cyclic, its order multiplies up to `#G`, vanishing of the period character is equivalent to no
extension, and the non-symplectic index is automatically tame.  The remaining geometric rigidity is
the future direction.
-/

open SuperspecialK3Symplectic

variable {G : Type*} [Group G] {k : Type*} [Field k]



/-
`[G : G_s] = #(im χ)`: the non-symplectic index is the order of the image of the period
character.
-/
theorem nonSymplecticIndex_eq_card_range (χ : G →* kˣ) :
    nonSymplecticIndex χ = Nat.card χ.range := by
  convert Subgroup.index_ker χ

/-
The **non-symplectic part `im χ ≅ G / G_s` is cyclic**: it is a finite subgroup of `kˣ`.
-/

/-
Bookkeeping: `#G = #G_s · [G : G_s]`.
-/

/-
**No non-trivial extension, equivalently stated.**  The whole group is symplectic
(`G = G_s`) iff the non-symplectic index is `1` iff the period character is trivial.
-/

/-
A trivial period character has non-symplectic index `1` (the trivial extension).
-/

/-
**Characteristic-`p` tameness of the non-symplectic part.**  In characteristic `p`, the
non-symplectic index `n = [G : G_s]` is never divisible by `p`: a finite subgroup of `kˣ` has order
prime to `p`, since `kˣ` has no non-trivial `p`-torsion in characteristic `p`.
-/

/-
Consequently, the non-symplectic index is coprime to the characteristic.
-/


open SuperspecialK3Symplectic in
theorem solution[Finite G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (χ : G →* kˣ) : ¬ (p ∣ nonSymplecticIndex χ) := by
  rw [nonSymplecticIndex_eq_card_range]
  intro hdvd
  haveI : Fintype χ.range := (Set.finite_range χ).fintype
  rw [Nat.card_eq_fintype_card] at hdvd
  -- Cauchy: a prime dividing the order yields an element of order `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := χ.range) p hdvd
  -- Its image in `k` is a `p`-th root of unity.
  have hg_pow : ((g : kˣ) : k) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one]
    simp
  -- In characteristic `p`, the only `p`-th root of unity is `1`: `(x - 1)ᵖ = xᵖ - 1 = 0`.
  have hx1 : ((g : kˣ) : k) = 1 := by
    have h0 : (((g : kˣ) : k) - 1) ^ p = 0 := by rw [sub_pow_char, hg_pow]; simp
    exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).pos.ne' |>.mp h0)
  -- Hence `g = 1`, contradicting `orderOf g = p ≠ 1`.
  have hg1 : (g : kˣ) = 1 := Units.val_eq_one.mp hx1
  have : g = 1 := Subtype.ext (by simp [hg1])
  rw [this, orderOf_one] at hg
  exact (Fact.out : p.Prime).ne_one hg.symm
