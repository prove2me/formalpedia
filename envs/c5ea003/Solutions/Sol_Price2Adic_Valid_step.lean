-- Prove2me | solution 1 for Price2Adic.Valid_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:32:08.784425+00:00
-- url     : https://prove2.me/submissions/32f398e0-38cd-4e8d-807f-19f5ce138a0d

-- Sol generated from Cryptography/Price2Adic/Tree.lean
import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Tree

/-!
# The Price tree of primitive Pythagorean triples: uniqueness and completeness

Price's ternary tree of primitive Pythagorean triples is usually presented by three
`3 × 3` matrices acting on triples `(a,b,c)`.  On the *parameter* side (Euclid's
`(m,n) ↦ (m²-n², 2mn, m²+n²)`) the three moves become the strikingly simple pair maps

* `A : (m,n) ↦ (m+n, 2n)`,
* `B : (m,n) ↦ (2m, m-n)`,
* `C : (m,n) ↦ (2m, m+n)`,

each of which *doubles* one of the two parameters.  This is the "halving alphabet":
every Price move is visible 2-adically, in contrast with the Berggren tree whose
moves are 3-adic in nature (`Catalog/Cryptography/BerggrenTrees`).

This file proves, for these maps, the two facts a brute-force enumeration can only
sample:

* **Well-definedness** (`Valid_step`): each move sends a valid Euclid parameter pair to
  a valid Euclid parameter pair.
* **Uniqueness** (`address_eval`, `eval_injective`): distinct words give distinct nodes —
  the tree has no duplicates.
* **Completeness** (`eval_address`): every valid parameter pair is reached.
* Together: `existsUnique_word` — every primitive Pythagorean triple has exactly one
  Price address; `evalEquiv` packages this as a bijection between Price words and
  valid parameter pairs.

We also prove two-sided *depth* bounds (`sum_le_of_length`, `sum_ge_of_length`)
quantifying that the Price tree grows at most geometrically with ratio `3` and at least
arithmetically with step `2`.  These are the rigorous form of the empirical
"`dP` grows like `log₂(m+n)`" law: the depth of the node `(m,n)` is squeezed
between `log₃(m+n) - 1` and `(m+n-3)/2`.

## Lab notes (round 70, exp 548)

BFS over the parameter tree from the root `(2,1)` to depth `8` produced
`(3^9-1)/2 = 9841` nodes, all distinct (`0` duplicates).  BFS pruned at `c ≤ 5000`
(maximal depth reached: `9`) produced exactly `792` nodes, matching a brute-force
enumeration of the primitive triples with `c ≤ 5000` with `0` missing and `0` extra.
The theorems below replace both finite checks by proofs.  The child triples of
`(3,4,5)` are `(5,12,13)`, `(15,8,17)`, `(7,24,25)` (`triple_children_root`), i.e. this
is the Price tree and not Berggren's, whose root children include `(21,20,29)`.
-/

open Price2Adic

/-! ## Arithmetic helpers -/

lemma odd_dvd_of_dvd_two_mul {d m : ℕ} (hd : d % 2 = 1) (h : d ∣ 2 * m) : d ∣ m := by
  have hc : Nat.Coprime 2 d := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
  exact hc.symm.dvd_of_dvd_mul_left (by simpa [Nat.mul_comm] using h)

lemma eq_one_of_dvd_gcd_eq_one {d x y : ℕ} (hg : Nat.gcd x y = 1) (h1 : d ∣ x) (h2 : d ∣ y) :
    d = 1 := Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd h1 h2)

lemma odd_of_dvd_odd {d x : ℕ} (h : d ∣ x) (hx : x % 2 = 1) : d % 2 = 1 := by
  rcases Nat.even_or_odd d with he | ho
  · have : (2 : ℕ) ∣ x := dvd_trans he.two_dvd h
    omega
  · exact Nat.odd_iff.mp ho

/-! ## The alphabet, the moves, and the nodes -/
















/-! ## Well-definedness -/



/-! ## The letter and the parent of a node -/









/-! ## Addresses: uniqueness and completeness -/















/-! ## Depth bounds (the rigorous `dP` law) -/





open Price2Adic in
theorem solution(l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) : Valid (step l p) := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, hg, hpar⟩ := hp
  cases l
  · refine ⟨by omega, by omega, ?_, by omega⟩
    show Nat.gcd (m + n) (2 * n) = 1
    set d := Nat.gcd (m + n) (2 * n) with hdef
    have h1 : d ∣ m + n := Nat.gcd_dvd_left _ _
    have h2 : d ∣ 2 * n := Nat.gcd_dvd_right _ _
    have h3 : d ∣ n := odd_dvd_of_dvd_two_mul (odd_of_dvd_odd h1 hpar) h2
    have h4 : d ∣ m := (Nat.dvd_add_right h3).mp (by simpa [Nat.add_comm] using h1)
    exact eq_one_of_dvd_gcd_eq_one hg h4 h3
  · refine ⟨by omega, by omega, ?_, by omega⟩
    show Nat.gcd (2 * m) (m - n) = 1
    set d := Nat.gcd (2 * m) (m - n) with hdef
    have h1 : d ∣ 2 * m := Nat.gcd_dvd_left _ _
    have h2 : d ∣ m - n := Nat.gcd_dvd_right _ _
    have hodd : (m - n) % 2 = 1 := by omega
    have h4 : d ∣ m := odd_dvd_of_dvd_two_mul (odd_of_dvd_odd h2 hodd) h1
    have h3 : d ∣ n := by
      have h := Nat.dvd_sub h4 h2
      have he : m - (m - n) = n := by omega
      rwa [he] at h
    exact eq_one_of_dvd_gcd_eq_one hg h4 h3
  · refine ⟨by omega, by omega, ?_, by omega⟩
    show Nat.gcd (2 * m) (m + n) = 1
    set d := Nat.gcd (2 * m) (m + n) with hdef
    have h1 : d ∣ 2 * m := Nat.gcd_dvd_left _ _
    have h2 : d ∣ m + n := Nat.gcd_dvd_right _ _
    have h4 : d ∣ m := odd_dvd_of_dvd_two_mul (odd_of_dvd_odd h2 hpar) h1
    have h3 : d ∣ n := (Nat.dvd_add_right h4).mp h2
    exact eq_one_of_dvd_gcd_eq_one hg h4 h3
