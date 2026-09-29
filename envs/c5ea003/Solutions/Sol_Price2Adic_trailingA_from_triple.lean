-- Prove2me | solution 1 for Price2Adic.trailingA_from_triple
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:12:07.79804+00:00
-- url     : https://prove2.me/submissions/da1149ec-0741-40d5-9a95-a3fd643314d3

import Mathlib
import Definitions.Def_Cryptography_Price2Adic_Runs
import Definitions.Def_Cryptography_Price2Adic_Tree

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Cryptography/Price2Adic/Tree.lean ====
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

namespace Price2Adic

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

-- [dropped: platform already declares PriceLetter]
-- [dropped: platform already declares PriceWord]
-- [dropped: platform already declares Valid]
-- [dropped: platform already declares step]
-- [dropped: platform already declares root]
-- [dropped: platform already declares eval]
-- [dropped: platform already declares triple]
-- [dropped: platform already declares oddLeg]
@[simp] theorem eval_nil : eval [] = root := rfl

theorem eval_append_one (w : PriceWord) (l : PriceLetter) :
    eval (w ++ [l]) = step l (eval w) := by
  simp [eval]

theorem root_valid : Valid root := by
  refine ⟨by norm_num, by norm_num, ?_, by norm_num⟩
  norm_num

/-- Root triple: `(3,4,5)`. -/
theorem triple_root : triple root = (3, 4, 5) := by norm_num [triple, root]

/-- The three children of the root are `(5,12,13)`, `(15,8,17)`, `(7,24,25)`: this is the
Price tree.  (Berggren's tree instead produces `(21,20,29)` among the root's children.) -/
theorem triple_children_root :
    triple (step .A root) = (5, 12, 13) ∧ triple (step .B root) = (15, 8, 17) ∧
      triple (step .C root) = (7, 24, 25) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [triple, step, root]

/-- Every valid parameter pair does give a Pythagorean triple. -/
theorem triple_isPythagorean (p : ℕ × ℕ) (hp : Valid p) :
    (triple p).1 ^ 2 + (triple p).2.1 ^ 2 = (triple p).2.2 ^ 2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨-, hlt, -, -⟩ := hp
  have h : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
  simp only [triple]
  zify [h]
  ring

/-! ## Well-definedness -/

theorem Valid_step (l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) : Valid (step l p) := by
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

theorem Valid_eval (w : PriceWord) : Valid (eval w) := by
  have key : ∀ (w : PriceWord) (p : ℕ × ℕ), Valid p →
      Valid (w.foldl (fun p l => step l p) p) := by
    intro w
    induction w with
    | nil => intro p hp; simpa using hp
    | cons l t ih => intro p hp; exact ih _ (Valid_step l p hp)
  exact key w root root_valid

/-! ## The letter and the parent of a node -/

-- [dropped: platform already declares letterOf]
-- [dropped: platform already declares parent]
theorem letterOf_step (l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) :
    letterOf (step l p) = l := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, hg, hpar⟩ := hp
  cases l <;> simp only [step, letterOf] <;> split_ifs <;> first | rfl | omega

theorem parent_step (l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) :
    parent (step l p) = p := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, hg, hpar⟩ := hp
  cases l <;> simp only [step, parent] <;> split_ifs <;>
    simp only [Prod.mk.injEq] <;> omega

/-- The parameter `n` of a valid non-root node is never `m/2`: the `B`/`C` split is
genuine. -/
theorem two_mul_ne (p : ℕ × ℕ) (hp : Valid p) (hroot : p ≠ root) : 2 * p.2 ≠ p.1 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, hg, hpar⟩ := hp
  intro h
  have hd : n ∣ Nat.gcd m n := Nat.dvd_gcd ⟨2, by omega⟩ dvd_rfl
  rw [hg] at hd
  have hn1 : n = 1 := Nat.dvd_one.mp hd
  exact hroot (by simp [root, Prod.ext_iff, hn1]; omega)

/-- Every valid node other than the root is the `letterOf`-child of its parent. -/
theorem step_letterOf_parent (p : ℕ × ℕ) (hp : Valid p) (hroot : p ≠ root) :
    step (letterOf p) (parent p) = p := by
  have hnm := two_mul_ne p hp hroot
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, hg, hpar⟩ := hp
  simp only at hnm
  simp only [letterOf, parent]
  split_ifs with h1 h2 <;> simp only [step, Prod.mk.injEq] <;> omega

theorem parent_valid (p : ℕ × ℕ) (hp : Valid p) (hroot : p ≠ root) : Valid (parent p) := by
  have hnm := two_mul_ne p hp hroot
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, hg, hpar⟩ := hp
  simp only at hnm
  simp only [parent]
  split_ifs with h1 h2
  · refine ⟨by omega, by omega, ?_, by omega⟩
    show Nat.gcd (m - n / 2) (n / 2) = 1
    set d := Nat.gcd (m - n / 2) (n / 2) with hdef
    have h3 : d ∣ n / 2 := Nat.gcd_dvd_right _ _
    have h3' : d ∣ n := dvd_trans h3 ⟨2, by omega⟩
    have h2' : d ∣ m - n / 2 := Nat.gcd_dvd_left _ _
    have h4 : d ∣ m := by
      have h := Nat.dvd_add h2' h3
      have he : m - n / 2 + n / 2 = m := by omega
      rwa [he] at h
    exact eq_one_of_dvd_gcd_eq_one hg h4 h3'
  · refine ⟨by omega, by omega, ?_, by omega⟩
    show Nat.gcd (m / 2) (m / 2 - n) = 1
    set d := Nat.gcd (m / 2) (m / 2 - n) with hdef
    have h4 : d ∣ m / 2 := Nat.gcd_dvd_left _ _
    have h2' : d ∣ m / 2 - n := Nat.gcd_dvd_right _ _
    have h4' : d ∣ m := dvd_trans h4 ⟨2, by omega⟩
    have h3 : d ∣ n := by
      have h := Nat.dvd_sub h4 h2'
      have he : m / 2 - (m / 2 - n) = n := by omega
      rwa [he] at h
    exact eq_one_of_dvd_gcd_eq_one hg h4' h3
  · refine ⟨by omega, by omega, ?_, by omega⟩
    show Nat.gcd (m / 2) (n - m / 2) = 1
    set d := Nat.gcd (m / 2) (n - m / 2) with hdef
    have h4 : d ∣ m / 2 := Nat.gcd_dvd_left _ _
    have h2' : d ∣ n - m / 2 := Nat.gcd_dvd_right _ _
    have h4' : d ∣ m := dvd_trans h4 ⟨2, by omega⟩
    have h3 : d ∣ n := by
      have h := Nat.dvd_add h2' h4
      have he : n - m / 2 + m / 2 = n := by omega
      rwa [he] at h
    exact eq_one_of_dvd_gcd_eq_one hg h4' h3

-- [dropped: platform already declares parent_sum_lt]
-- [dropped: platform already declares address]
@[simp] theorem address_root : address root = [] := by
  rw [address]; simp

/-- **Completeness**: every valid parameter pair is a node of the Price tree. -/
theorem eval_address (p : ℕ × ℕ) (hp : Valid p) : eval (address p) = p := by
  induction hs : p.1 + p.2 using Nat.strong_induction_on generalizing p with
  | _ s ih =>
    subst hs
    by_cases hroot : p = root
    · subst hroot; simp
    · rw [address, dif_pos ⟨hp, hroot⟩, eval_append_one,
        ih _ (parent_sum_lt p hp hroot) (parent p) (parent_valid p hp hroot) rfl]
      exact step_letterOf_parent p hp hroot

theorem sum_step_ge (l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) :
    p.1 + p.2 + 2 ≤ (step l p).1 + (step l p).2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  cases l <;> simp only [step] <;> omega

theorem sum_step_le (l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) :
    (step l p).1 + (step l p).2 ≤ 3 * (p.1 + p.2) := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  cases l <;> simp only [step] <;> omega

theorem Valid.three_le {p : ℕ × ℕ} (hp : Valid p) : 3 ≤ p.1 + p.2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  omega

theorem sum_root_le (w : PriceWord) : 3 ≤ (eval w).1 + (eval w).2 := (Valid_eval w).three_le

theorem step_ne_root (l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) : step l p ≠ root := by
  intro h
  have h2 := sum_step_ge l p hp
  have h3 := hp.three_le
  rw [h] at h2
  simp only [root] at h2
  omega

theorem eval_append_one_ne_root (w : PriceWord) (l : PriceLetter) : eval (w ++ [l]) ≠ root := by
  rw [eval_append_one]
  exact step_ne_root l (eval w) (Valid_eval w)

/-- Unfolding lemma for `address` at a non-root node. -/
theorem address_of_ne_root (p : ℕ × ℕ) (hp : Valid p) (h : p ≠ root) :
    address p = address (parent p) ++ [letterOf p] := by
  rw [address, dif_pos ⟨hp, h⟩]

/-- **Uniqueness**: the address of the node addressed by `w` is `w` itself; no two Price
words collide. -/
theorem address_eval (w : PriceWord) : address (eval w) = w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton t l ih =>
    have hvt : Valid (eval t) := Valid_eval t
    have hv : Valid (step l (eval t)) := Valid_step l _ hvt
    have hne : step l (eval t) ≠ root := step_ne_root l _ hvt
    rw [eval_append_one, address_of_ne_root _ hv hne, parent_step l (eval t) hvt,
      letterOf_step l (eval t) hvt, ih]

theorem eval_injective : Function.Injective eval := by
  intro w w' h
  have h2 := congrArg address h
  rwa [address_eval, address_eval] at h2

/-- Every primitive parameter pair has **exactly one** Price address: the Price tree is a
tree (no duplicates) and it exhausts the primitive Pythagorean triples (no gaps). -/
theorem existsUnique_word (p : ℕ × ℕ) (hp : Valid p) : ∃! w : PriceWord, eval w = p :=
  ⟨address p, eval_address p hp, fun w hw => by rw [← hw, address_eval]⟩

/-- The Price tree as an explicit bijection: Price words ↔ primitive Euclid parameters. -/
def evalEquiv : PriceWord ≃ {p : ℕ × ℕ // Valid p} where
  toFun w := ⟨eval w, Valid_eval w⟩
  invFun p := address p.1
  left_inv w := address_eval w
  right_inv p := Subtype.ext (eval_address p.1 p.2)

/-! ## Depth bounds (the rigorous `dP` law) -/

/-- Geometric upper bound: a node at depth `d` has parameter sum at most `3^(d+1)`;
equivalently the depth is at least `log₃(m+n) - 1`. -/
theorem sum_le_of_length (w : PriceWord) : (eval w).1 + (eval w).2 ≤ 3 ^ (w.length + 1) := by
  induction w using List.reverseRecOn with
  | nil => norm_num [eval, root]
  | append_singleton t l ih =>
    rw [eval_append_one]
    calc (step l (eval t)).1 + (step l (eval t)).2 ≤ 3 * ((eval t).1 + (eval t).2) :=
          sum_step_le l _ (Valid_eval t)
      _ ≤ 3 * 3 ^ (t.length + 1) := by omega
      _ = 3 ^ ((t ++ [l]).length + 1) := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          ring

/-- Arithmetic lower bound: a node at depth `d` has parameter sum at least `2d + 3`;
equivalently the depth is at most `(m+n-3)/2`. -/
theorem sum_ge_of_length (w : PriceWord) : 2 * w.length + 3 ≤ (eval w).1 + (eval w).2 := by
  induction w using List.reverseRecOn with
  | nil => norm_num [eval, root]
  | append_singleton t l ih =>
    rw [eval_append_one]
    have h := sum_step_ge l (eval t) (Valid_eval t)
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- The Price depth of a node is squeezed logarithmically: with `s = m + n`,
`log₃ s - 1 ≤ depth ≤ (s - 3)/2`.  This is the proved form of the empirical `dP` law. -/
theorem depth_squeeze (p : ℕ × ℕ) (hp : Valid p) :
    p.1 + p.2 ≤ 3 ^ ((address p).length + 1) ∧
      2 * (address p).length + 3 ≤ p.1 + p.2 := by
  constructor
  · have h := sum_le_of_length (address p)
    rwa [eval_address p hp] at h
  · have h := sum_ge_of_length (address p)
    rwa [eval_address p hp] at h

end Price2Adic
-- ==== upstream: Packages/Catalog/Cryptography/Price2Adic/Letters.lean ====
/-!
# The Price alphabet is a 2-adic dial — exactly two letters deep

The Price moves double a parameter, so one expects the address of a node to be readable
from the 2-adic expansion of its triple.  This file makes that precise **and** locates
the exact point where the 2-adic reading stops.

Write `N = oddLeg (m,n) = m² - n²` for the odd leg of the triple of a node, and read a
Price address from the leaf backwards (position `0` = last letter).

* `oddLeg_odd` — `N` is always odd: **the modulus `2` is vacuous**, no information.
* `letter_pos0_iff` — position `0` is `A` **iff** `N ≡ 1 (mod 4)` (and `B`/`C` iff
  `N ≡ 3 (mod 4)`).  A single bit of `N mod 4` determines the last letter.
* `letter_pos1_iff` — position `1` is `A` **iff** `N mod 8 ∈ {1,3}`.  A second bit,
  living in `N mod 8`, determines the previous letter.
* `letter_pos0_pos1_table` — the full `N mod 8` dictionary of the last two letters.
* `twoAdic_blind_BC` — **sharpness**: the `B`/`C` distinction is 2-adically invisible.
  For *every* `k` there are two Price nodes, one a `B`-child and one a `C`-child, whose
  three triple entries agree modulo `2^k`.  Consequently no function of any 2-adic
  residue of the triple can separate `B` from `C`.

So the halving alphabet is a *residue dial of exactly two symbols*: `N mod 8` reads two
letters and nothing more, and the residual ternary choice is invisible at `2`.  This is
the complement of the Berggren picture, whose moves are 3-adic.

## Lab notes (round 70, exp 548)

BFS to depth `8` (`9841` nodes).  For `j = 1, 2` (positions counted from the leaf) the
predicate "letter at position `j` is `A`" is a function of `N mod 2^(j+1)` — a perfect
classifier, and `2^(j+1)` is the smallest such modulus.  For `j = 3, 4, 5` no modulus
`2^k` with `k ≤ 10` classifies: some class always splits.
Tabulated dictionary at `N mod 16` (letters read from the leaf):
`1,9 ↦ AA`, `3,11 ↦ A{B,C}`, `5,13 ↦ {B,C}A`, `7,15 ↦ {B,C}{B,C}`.
`twoAdic_blind_BC` explains the `j ≥ 3` failure at its source: the residual `B`/`C` bit
never enters the 2-adic filtration at all.
-/

namespace Price2Adic

/-! ## The odd leg -/

theorem oddLeg_eq (m n : ℕ) : oddLeg (m, n) = m ^ 2 - n ^ 2 := rfl

/-- `N = m² - n²` is odd for every primitive parameter pair: the modulus `2` carries no
information about the Price address. -/
theorem oddLeg_odd (p : ℕ × ℕ) (hp : Valid p) : oddLeg p % 2 = 1 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, hpar⟩ := hp
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hlt.le 2
  have key : oddLeg (m, n) + n ^ 2 = m ^ 2 := by
    simp only [oddLeg_eq]; omega
  rcases Nat.even_or_odd m with hm | hm
  · -- m even, n odd
    obtain ⟨s, hs⟩ := hm
    have hn2 : n % 2 = 1 := by omega
    obtain ⟨t, ht⟩ : ∃ t, n = 2 * t + 1 := ⟨n / 2, by omega⟩
    have h1 : m ^ 2 = 4 * (s * s) := by subst hs; ring
    have h2 : n ^ 2 = 4 * (t * t + t) + 1 := by subst ht; ring
    omega
  · obtain ⟨s, hs⟩ := hm
    have hn2 : n % 2 = 0 := by omega
    obtain ⟨t, ht⟩ : ∃ t, n = 2 * t := ⟨n / 2, by omega⟩
    have h1 : m ^ 2 = 4 * (s * s + s) + 1 := by subst hs; ring
    have h2 : n ^ 2 = 4 * (t * t) := by subst ht; ring
    omega

/-! ## Position 0: the modulus 4 -/

theorem letterOf_eq_A_iff (p : ℕ × ℕ) : letterOf p = .A ↔ p.2 % 2 = 0 := by
  obtain ⟨m, n⟩ := p
  simp only [letterOf]
  split_ifs with h1 h2 <;> simp_all

theorem letterOf_pair_eq_A_iff (m n : ℕ) : letterOf (m, n) = .A ↔ n % 2 = 0 :=
  letterOf_eq_A_iff (m, n)

theorem letterOf_pair_ne_A_iff (m n : ℕ) : letterOf (m, n) ≠ .A ↔ n % 2 = 1 := by
  rw [ne_eq, letterOf_pair_eq_A_iff]
  omega

/-- **Position 0 law.** The last letter of the Price address of a node is `A` exactly
when its odd leg is `1 mod 4`; it is `B` or `C` exactly when the odd leg is `3 mod 4`. -/
theorem oddLeg_mod_four (p : ℕ × ℕ) (hp : Valid p) :
    (letterOf p = .A ∧ oddLeg p % 4 = 1) ∨ (letterOf p ≠ .A ∧ oddLeg p % 4 = 3) := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, hpar⟩ := hp
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hlt.le 2
  have key : oddLeg (m, n) + n ^ 2 = m ^ 2 := by simp only [oddLeg_eq]; omega
  rcases Nat.even_or_odd n with hne | hno
  · left
    obtain ⟨t, ht⟩ := hne
    obtain ⟨s, hs⟩ : ∃ s, m = 2 * s + 1 := ⟨m / 2, by omega⟩
    have h1 : m ^ 2 = 4 * (s * s + s) + 1 := by subst hs; ring
    have h2 : n ^ 2 = 4 * (t * t) := by subst ht; ring
    exact ⟨(letterOf_eq_A_iff (m, n)).mpr (by simp only; omega), by omega⟩
  · right
    obtain ⟨t, ht⟩ := hno
    obtain ⟨s, hs⟩ : ∃ s, m = 2 * s := ⟨m / 2, by omega⟩
    have h1 : m ^ 2 = 4 * (s * s) := by subst hs; ring
    have h2 : n ^ 2 = 4 * (t * t + t) + 1 := by subst ht; ring
    refine ⟨fun hA => ?_, by omega⟩
    have := (letterOf_eq_A_iff (m, n)).mp hA
    simp only at this
    omega

theorem letterOf_eq_A_iff_oddLeg (p : ℕ × ℕ) (hp : Valid p) :
    letterOf p = .A ↔ oddLeg p % 4 = 1 := by
  rcases oddLeg_mod_four p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · constructor
    · intro h; exact absurd h h1
    · intro h; omega

/-- Read from the leaf, position `0` of the address of `eval (w ++ [l])` is `l`, and it is
`A` exactly when the odd leg is `1 mod 4`. -/
theorem letter_pos0_iff (w : PriceWord) (l : PriceLetter) :
    l = .A ↔ oddLeg (eval (w ++ [l])) % 4 = 1 := by
  have hv : Valid (eval (w ++ [l])) := Valid_eval _
  have hl : letterOf (eval (w ++ [l])) = l := by
    rw [eval_append_one]; exact letterOf_step l _ (Valid_eval w)
  have h := letterOf_eq_A_iff_oddLeg _ hv
  rwa [hl] at h

/-! ## Position 1: the modulus 8 -/

/-- **Position 1 law.** The letter one step above the leaf is `A` exactly when the odd leg
of the leaf lies in `{1, 3} mod 8`. -/
theorem letterOf_parent_eq_A_iff (p : ℕ × ℕ) (hp : Valid p) :
    letterOf (parent p) = .A ↔ (oddLeg p % 8 = 1 ∨ oddLeg p % 8 = 3) := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, hpar⟩ := hp
  have hle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hlt.le 2
  have key : oddLeg (m, n) + n ^ 2 = m ^ 2 := by simp only [oddLeg_eq]; omega
  rcases Nat.even_or_odd n with hne | hno
  · -- `n` even, `m` odd; parent is `(m - n/2, n/2)`, an `A`-child iff `4 ∣ n`
    obtain ⟨t, ht⟩ := hne
    obtain ⟨s, hs⟩ : ∃ s, m = 2 * s + 1 := ⟨m / 2, by omega⟩
    have hm2 : m ^ 2 = 8 * (s * (s + 1) / 2) + 1 := by
      have hev : 2 ∣ s * (s + 1) := (Nat.even_mul_succ_self s).two_dvd
      obtain ⟨u, hu⟩ := hev
      subst hs
      rw [hu]
      have : (2 * u) / 2 = u := by omega
      rw [this]
      nlinarith [hu]
    have hpar' : parent (m, n) = (m - n / 2, n / 2) := by
      simp only [parent]; rw [if_pos (by omega)]
    rw [hpar', letterOf_eq_A_iff]
    simp only
    rcases Nat.even_or_odd t with hte | hto
    · obtain ⟨r, hr⟩ := hte
      have hn2 : n ^ 2 = 16 * (r * r) := by subst ht; subst hr; ring
      constructor
      · intro _; left; omega
      · intro _; omega
    · obtain ⟨r, hr⟩ := hto
      have hn2 : n ^ 2 = 8 * (2 * (r * r + r)) + 4 := by subst ht; subst hr; ring
      constructor
      · intro h; omega
      · intro h; omega
  · -- `n` odd, `m` even; parent is `(m/2, ·)`, an `A`-child iff `m/2` is odd
    obtain ⟨t, ht⟩ := hno
    obtain ⟨s, hs⟩ : ∃ s, m = 2 * s := ⟨m / 2, by omega⟩
    have hn2 : n ^ 2 = 8 * ((t * (t + 1)) / 2) + 1 := by
      have hev : 2 ∣ t * (t + 1) := (Nat.even_mul_succ_self t).two_dvd
      obtain ⟨u, hu⟩ := hev
      subst ht
      rw [hu]
      have : (2 * u) / 2 = u := by omega
      rw [this]
      nlinarith [hu]
    have hms : m / 2 = s := by omega
    have hpar' : (parent (m, n) = (m / 2, m / 2 - n) ∧ 2 * n < m) ∨
        (parent (m, n) = (m / 2, n - m / 2) ∧ m ≤ 2 * n) := by
      simp only [parent]
      rw [if_neg (by omega)]
      by_cases h : 2 * n < m
      · exact Or.inl ⟨by rw [if_pos h], h⟩
      · exact Or.inr ⟨by rw [if_neg h], by omega⟩
    rcases Nat.even_or_odd s with hse | hso
    · -- `m/2` even: the parent is a `B`/`C`-child and `N ≡ 7 mod 8`
      obtain ⟨r, hr⟩ := hse
      have hm2 : m ^ 2 = 8 * (2 * (r * r)) := by subst hs; subst hr; ring
      have hNval : oddLeg (m, n) % 8 = 7 := by omega
      have : letterOf (parent (m, n)) ≠ .A := by
        rcases hpar' with ⟨h, hbc⟩ | ⟨h, hbc⟩ <;> rw [h, letterOf_pair_ne_A_iff] <;> omega
      constructor
      · intro h; exact absurd h this
      · intro h; omega
    · -- `m/2` odd: the parent is an `A`-child and `N ≡ 3 mod 8`
      obtain ⟨r, hr⟩ := hso
      have hm2 : m ^ 2 = 8 * (2 * (r * r + r)) + 4 := by subst hs; subst hr; ring
      have hNval : oddLeg (m, n) % 8 = 3 := by omega
      have : letterOf (parent (m, n)) = .A := by
        rcases hpar' with ⟨h, hbc⟩ | ⟨h, hbc⟩ <;> rw [h, letterOf_pair_eq_A_iff] <;> omega
      simp [this, hNval]

/-- Read from the leaf, position `1` of the address of `eval (w ++ [l₁, l₂])` is `l₁`,
and it is `A` exactly when the odd leg of the leaf lies in `{1,3} mod 8`. -/
theorem letter_pos1_iff (w : PriceWord) (l₁ l₂ : PriceLetter) :
    l₁ = .A ↔ (oddLeg (eval (w ++ [l₁, l₂])) % 8 = 1 ∨
      oddLeg (eval (w ++ [l₁, l₂])) % 8 = 3) := by
  have hw1 : Valid (eval (w ++ [l₁])) := Valid_eval _
  have hnode : eval (w ++ [l₁, l₂]) = step l₂ (eval (w ++ [l₁])) := by
    have : w ++ [l₁, l₂] = (w ++ [l₁]) ++ [l₂] := by simp
    rw [this, eval_append_one]
  have hpar : parent (eval (w ++ [l₁, l₂])) = eval (w ++ [l₁]) := by
    rw [hnode]; exact parent_step l₂ _ hw1
  have hl : letterOf (eval (w ++ [l₁])) = l₁ := by
    rw [eval_append_one]; exact letterOf_step l₁ _ (Valid_eval w)
  have h := letterOf_parent_eq_A_iff (eval (w ++ [l₁, l₂])) (Valid_eval _)
  rw [hpar, hl] at h
  exact h

/-- The two-letter dictionary at the leaf: `N mod 8` determines the pair
(position 1 is `A`?, position 0 is `A`?) — and nothing finer, by `twoAdic_blind_BC`. -/
theorem letter_pos0_pos1_table (w : PriceWord) (l₁ l₂ : PriceLetter) :
    (oddLeg (eval (w ++ [l₁, l₂])) % 8 = 1 ↔ (l₁ = .A ∧ l₂ = .A)) ∧
    (oddLeg (eval (w ++ [l₁, l₂])) % 8 = 3 ↔ (l₁ = .A ∧ l₂ ≠ .A)) ∧
    (oddLeg (eval (w ++ [l₁, l₂])) % 8 = 5 ↔ (l₁ ≠ .A ∧ l₂ = .A)) ∧
    (oddLeg (eval (w ++ [l₁, l₂])) % 8 = 7 ↔ (l₁ ≠ .A ∧ l₂ ≠ .A)) := by
  have hnode : w ++ [l₁, l₂] = (w ++ [l₁]) ++ [l₂] := by simp
  have h0 : l₂ = .A ↔ oddLeg (eval (w ++ [l₁, l₂])) % 8 % 4 = 1 := by
    rw [hnode] at *
    have := letter_pos0_iff (w ++ [l₁]) l₂
    rw [this]
    constructor
    · intro h; omega
    · intro h; omega
  have h1 := letter_pos1_iff w l₁ l₂
  have hodd : oddLeg (eval (w ++ [l₁, l₂])) % 2 = 1 :=
    oddLeg_odd _ (Valid_eval _)
  set N := oddLeg (eval (w ++ [l₁, l₂])) % 8 with hN
  have hNlt : N < 8 := by omega
  have hNodd : N % 2 = 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> constructor <;> intro h
  · exact ⟨h1.mpr (Or.inl h), h0.mpr (by omega)⟩
  · have ha := h1.mp h.1
    have hb : N % 4 = 1 := by have := h0.mp h.2; omega
    omega
  · exact ⟨h1.mpr (Or.inr h), fun hc => by have := h0.mp hc; omega⟩
  · have ha := h1.mp h.1
    have hb : N % 4 ≠ 1 := fun hc => h.2 (h0.mpr (by omega))
    omega
  · refine ⟨fun hc => ?_, h0.mpr (by omega)⟩
    have := h1.mp hc
    omega
  · have ha : ¬ (N = 1 ∨ N = 3) := fun hc => h.1 (h1.mpr hc)
    have hb : N % 4 = 1 := by have := h0.mp h.2; omega
    omega
  · refine ⟨fun hc => by have := h1.mp hc; omega, fun hc => by have := h0.mp hc; omega⟩
  · have ha : ¬ (N = 1 ∨ N = 3) := fun hc => h.1 (h1.mpr hc)
    have hb : N % 4 ≠ 1 := fun hc => h.2 (h0.mpr (by omega))
    omega

/-! ## Sharpness: `B` versus `C` is 2-adically invisible -/

theorem oddLeg_step_B (p : ℕ × ℕ) (hp : Valid p) :
    oddLeg (step .B p) = oddLeg (step .C p) + 4 * p.1 * p.2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  have h1 : (m - n) ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (m + n) ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  simp only [step, oddLeg_eq]
  zify [h1, h2, hlt.le]
  ring

theorem hyp_step_C (p : ℕ × ℕ) (hp : Valid p) :
    (triple (step .C p)).2.2 = (triple (step .B p)).2.2 + 4 * p.1 * p.2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  simp only [step, triple]
  zify [hlt.le]
  ring

theorem evenLeg_step_C (p : ℕ × ℕ) (hp : Valid p) :
    (triple (step .C p)).2.1 = (triple (step .B p)).2.1 + 8 * p.1 * p.2 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, -⟩ := hp
  simp only [step, triple]
  zify [hlt.le]
  ring

/-- **Sharpness of the 2-adic reading.**  For every `k` there is a `B`-child and a
`C`-child of the Price tree whose three triple entries agree modulo `2^k`.  Hence no
function of the 2-adic residues of a triple can decide the `B`/`C` letter: the halving
alphabet is a residue dial of exactly two symbols (`A` versus not-`A`, twice). -/
theorem twoAdic_blind_BC (k : ℕ) :
    ∃ p q : ℕ × ℕ, Valid p ∧ Valid q ∧ letterOf p = .B ∧ letterOf q = .C ∧
      (triple p).1 % 2 ^ k = (triple q).1 % 2 ^ k ∧
      (triple p).2.1 % 2 ^ k = (triple q).2.1 % 2 ^ k ∧
      (triple p).2.2 % 2 ^ k = (triple q).2.2 % 2 ^ k := by
  set r : ℕ × ℕ := (2 ^ k + 1, 2 ^ k) with hr
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
  have hrv : Valid r := by
    refine ⟨by simp [hpos], by simp, ?_, ?_⟩
    · show Nat.gcd (2 ^ k + 1) (2 ^ k) = 1
      simp [Nat.gcd_comm]
    · show (2 ^ k + 1 + 2 ^ k) % 2 = 1
      have : (2 : ℕ) ∣ 2 ^ k + 2 ^ k := ⟨2 ^ k, by ring⟩
      omega
  refine ⟨step .B r, step .C r, Valid_step _ _ hrv, Valid_step _ _ hrv,
    letterOf_step _ _ hrv, letterOf_step _ _ hrv, ?_, ?_, ?_⟩
  · have h := oddLeg_step_B r hrv
    have hd : 4 * r.1 * r.2 = 2 ^ k * (4 * r.1) := by simp only [hr]; ring
    have hA : (triple (step .B r)).1 = oddLeg (step .B r) := by
      obtain ⟨a, b⟩ := step .B r; rfl
    have hC : (triple (step .C r)).1 = oddLeg (step .C r) := by
      obtain ⟨a, b⟩ := step .C r; rfl
    rw [hA, hC, h, hd, Nat.add_mul_mod_self_left]
  · have h := evenLeg_step_C r hrv
    have hd : 8 * r.1 * r.2 = 2 ^ k * (8 * r.1) := by simp only [hr]; ring
    rw [h, hd, Nat.add_mul_mod_self_left]
  · have h := hyp_step_C r hrv
    have hd : 4 * r.1 * r.2 = 2 ^ k * (4 * r.1) := by simp only [hr]; ring
    rw [h, hd, Nat.add_mul_mod_self_left]

end Price2Adic
-- ==== upstream: Packages/Catalog/Cryptography/Price2Adic/Runs.lean ====
/-!
# The trailing `A`-run is a 2-adic valuation

`Letters.lean` showed that `N mod 4` and `N mod 8` read the last two letters of a Price
address and that no 2-adic residue reads more.  This file identifies what the *whole*
2-adic filtration does read: the length of the terminal block of `A`'s.

* `trailingA_eq_padicValNat` — for every Price word `w`, the number of trailing `A`'s of
  `w` equals `v₂(n)`, the 2-adic valuation of the smaller Euclid parameter of the node
  `eval w`.  The halving alphabet is literally a 2-adic valuation counter.
* `trailingA_address` — the same statement read off a node.
* `trailingA_from_triple` — the triple-level form: the trailing `A`-run of the address of
  a node with triple `(a, b, c)` is `v₂(b) - 1` when `a ≡ 1 (mod 4)`, and `0` when
  `a ≡ 3 (mod 4)`.  Everything is observable from the triple, with no reference to the
  Euclid parameters.

Combined with `twoAdic_blind_BC`, this is the exact 2-adic content of a Price address:
the terminal `A`-run, and nothing else.

## Lab notes (round 70, exp 548)

BFS to depth `8`: for all `9841` nodes the trailing-`A` count matched `v₂(n)` and
matched `v₂(b) - 1` whenever the odd leg was `1 mod 4` (`0` otherwise), with no
exceptions.  Root case: address `[]`, `n = 1`, `v₂ = 0`.
-/

namespace Price2Adic

-- [dropped: platform already declares trailingA]
@[simp] theorem trailingA_nil : trailingA [] = 0 := rfl

@[simp] theorem trailingA_append_A (w : PriceWord) :
    trailingA (w ++ [.A]) = trailingA w + 1 := by
  simp [trailingA]

@[simp] theorem trailingA_append_B (w : PriceWord) : trailingA (w ++ [.B]) = 0 := by
  simp [trailingA]

@[simp] theorem trailingA_append_C (w : PriceWord) : trailingA (w ++ [.C]) = 0 := by
  simp [trailingA]

theorem padicValNat_two_mul (n : ℕ) (hn : 0 < n) :
    padicValNat 2 (2 * n) = padicValNat 2 n + 1 := by
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
  omega

theorem padicValNat_odd {n : ℕ} (hn : n % 2 = 1) : padicValNat 2 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

/-- One Price move raises `v₂(n)` by one (letter `A`) or resets it to zero (`B`, `C`). -/
theorem padicValNat_step (l : PriceLetter) (p : ℕ × ℕ) (hp : Valid p) :
    padicValNat 2 (step l p).2 = if l = .A then padicValNat 2 p.2 + 1 else 0 := by
  obtain ⟨m, n⟩ := p
  obtain ⟨hn, hlt, -, hpar⟩ := hp
  cases l
  · simpa only [step, if_pos rfl] using padicValNat_two_mul n hn
  · simpa only [step, reduceIte] using padicValNat_odd (n := m - n) (by omega)
  · simpa only [step, reduceIte] using padicValNat_odd (n := m + n) (by omega)

/-- **The `A`-run law.**  The trailing `A`-run of a Price address is exactly the 2-adic
valuation of the smaller Euclid parameter of the node it addresses. -/
theorem trailingA_eq_padicValNat (w : PriceWord) :
    trailingA w = padicValNat 2 (eval w).2 := by
  induction w using List.reverseRecOn with
  | nil => simp [eval, root]
  | append_singleton t l ih =>
    have hstep := padicValNat_step l (eval t) (Valid_eval t)
    rw [eval_append_one]
    cases l
    · rw [trailingA_append_A, ih, hstep, if_pos rfl]
    · rw [trailingA_append_B, hstep]; simp
    · rw [trailingA_append_C, hstep]; simp

/-- Node form of the `A`-run law. -/
theorem trailingA_address (p : ℕ × ℕ) (hp : Valid p) :
    trailingA (address p) = padicValNat 2 p.2 := by
  have h := trailingA_eq_padicValNat (address p)
  rwa [eval_address p hp] at h

/-- **Triple-level `A`-run law.**  For a node with triple `(a, b, c)`, the trailing
`A`-run of its Price address is `v₂(b) - 1` when `a ≡ 1 (mod 4)` and `0` when
`a ≡ 3 (mod 4)`: the run is read off the even leg alone, with the mod-4 class of the odd
leg deciding whether the reading applies. -/
theorem trailingA_from_triple (p : ℕ × ℕ) (hp : Valid p) :
    trailingA (address p) =
      (if oddLeg p % 4 = 1 then padicValNat 2 (triple p).2.1 - 1 else 0) := by
  have hrun := trailingA_address p hp
  have hA := letterOf_eq_A_iff_oddLeg p hp
  have hA' := letterOf_eq_A_iff p
  obtain ⟨hn, hlt, hg, hpar⟩ := hp
  obtain ⟨m, n⟩ := p
  simp only at hA hA' hrun ⊢
  by_cases h4 : oddLeg (m, n) % 4 = 1
  · -- `n` even, `m` odd
    have hne : n % 2 = 0 := hA'.mp (hA.mpr h4)
    have hb : (triple (m, n)).2.1 = 2 * (m * n) := by simp only [triple]; ring
    have hmodd : m % 2 = 1 := by omega
    have hval : padicValNat 2 (m * n) = padicValNat 2 n := by
      rw [padicValNat.mul (p := 2) (by omega) (by omega), padicValNat_odd hmodd]
      simp
    rw [if_pos h4, hb, padicValNat_two_mul _ (Nat.mul_pos (by omega) hn), hval, hrun]
    omega
  · -- `n` odd
    have hne : n % 2 = 1 := by
      by_contra hc
      exact h4 (hA.mp (hA'.mpr (by omega)))
    rw [if_neg h4, hrun, padicValNat_odd hne]

end Price2Adic
section
open Price2Adic

theorem solution (p : ℕ × ℕ) (hp : Valid p) :
    trailingA (address p) =
      (if oddLeg p % 4 = 1 then padicValNat 2 (triple p).2.1 - 1 else 0) :=
  Price2Adic.trailingA_from_triple p hp

end
