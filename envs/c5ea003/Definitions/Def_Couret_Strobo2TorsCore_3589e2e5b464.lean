-- Prove2me | Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
-- name    : Couret_Strobo2TorsCore_3589e2e5b464
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:26.648298+00:00
-- url     : https://prove2.me/theorems/2bf163f9-ae93-4df2-9111-adb6fc6cc82a
-- title:
--   Ordered triple squares and their two partner mechanisms
-- statement:
--   Defines diagonal and off-diagonal sum counts for triples, ordered-square counts for finite supports, and translation. Ordinary partners differ by a two-torsion translation. Exceptional partners have the form $\{a,b,b+d\}$ and a two-torsion translate of $\{a,2b-a,2b-a+d\}$, where $d\ne0$, $2d=0$, $2a\ne2b$, and $3(b-a)\in\{0,d\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/Strobo2TorsCore.lean; source file SHA-256 8c32a0fc004922553a9d42003aa4c0c8c9a6b30d8a906ee36d61566951be18b5

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega
import Aesop

set_option autoImplicit false

/-!
STROBO-2TORS: ordered-square classification of three-element finite supports.

This file establishes an assembled equivalence for the actual ordered-square
coefficient of cardinality-three Finsets, with every doubling profile and
relabelling handled internally. Exceptional partners are not related by any
ambient-group translation. It does NOT establish formal cardinality/counting
theorems, independent mathematical validation, or a novelty claim.

The coefficient below is the explicit nine-ordered-pair expansion of the
convolution square of a three-element support {a,b,c}, when its entries are
pairwise distinct. Thus diagonal terms have coefficient 1 and the three
off-diagonal pair sums have coefficient 2.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Diagonal terms in a three-point ordered convolution square. -/
def diagCoeff (a b c z : G) : ℕ :=
  (if a + a = z then 1 else 0) +
  (if b + b = z then 1 else 0) +
  (if c + c = z then 1 else 0)

/-- The three unordered off-diagonal pairs. -/
def offCoeff (a b c z : G) : ℕ :=
  (if a + b = z then 1 else 0) +
  (if a + c = z then 1 else 0) +
  (if b + c = z then 1 else 0)

/-- The explicit nine-ordered-pair coefficient; valid for distinct a,b,c. -/
def tripleSquareCoeff (a b c z : G) : ℕ :=
  diagCoeff a b c z + 2 * offCoeff a b c z

/-- Translating both summands by a 2-torsion element preserves their sum. -/
theorem pair_sum_translate (a b u : G) (hu : u + u = 0) :
    (a + u) + (b + u) = a + b := by
  calc
    (a + u) + (b + u) = (a + b) + (u + u) := by abel
    _ = a + b := by simp [hu]

/-- A square coefficient is invariant under simultaneous 2-torsion translation. -/
theorem diagCoeff_translate (a b c u z : G) (hu : u + u = 0) :
    diagCoeff (a + u) (b + u) (c + u) z = diagCoeff a b c z := by
  simp only [diagCoeff, pair_sum_translate a a u hu,
    pair_sum_translate b b u hu, pair_sum_translate c c u hu]

theorem offCoeff_translate (a b c u z : G) (hu : u + u = 0) :
    offCoeff (a + u) (b + u) (c + u) z = offCoeff a b c z := by
  simp only [offCoeff, pair_sum_translate a b u hu,
    pair_sum_translate a c u hu, pair_sum_translate b c u hu]

theorem tripleSquareCoeff_translate (a b c u z : G) (hu : u + u = 0) :
    tripleSquareCoeff (a + u) (b + u) (c + u) z =
      tripleSquareCoeff a b c z := by
  unfold tripleSquareCoeff
  rw [diagCoeff_translate a b c u z hu, offCoeff_translate a b c u z hu]

/-- Reduction modulo two removes the six ordered off-diagonal contributions. -/
theorem tripleSquareCoeff_mod_two (a b c z : G) :
    tripleSquareCoeff a b c z % 2 = diagCoeff a b c z % 2 := by
  unfold tripleSquareCoeff
  omega

/-- Equality of doubling images is exactly membership of a difference in G[2]. -/
theorem double_eq_iff_two_torsion (a b : G) :
    a + a = b + b ↔ (b - a) + (b - a) = 0 := by
  constructor
  · intro h
    calc
      (b - a) + (b - a) = (b + b) - (a + a) := by abel
      _ = 0 := by rw [h]; simp
  · intro h
    have hzero : (b + b) - (a + a) = 0 := by
      calc
        (b + b) - (a + a) = (b - a) + (b - a) := by abel
        _ = 0 := h
    exact (sub_eq_zero.mp hzero).symm



/-- Unordered three-point support has sum a+b+c when entries are distinct. -/
private theorem sum_three
    (a b c : G) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset G).sum id = a + b + c := by
  simp [hab, hac, hbc, add_assoc, add_comm, add_left_comm]



/--
All possible multiplicity patterns of three doubling images.
One case has multiplicity 3; three cases have pattern (2,1);
the final case has pattern (1,1,1).
-/
theorem three_doubling_profiles (a b c : G) :
    (a + a = b + b ∧ b + b = c + c) ∨
    (a + a = b + b ∧ b + b ≠ c + c) ∨
    (a + a ≠ b + b ∧ a + a = c + c) ∨
    (a + a ≠ b + b ∧ a + a ≠ c + c ∧ b + b = c + c) ∨
    (a + a ≠ b + b ∧ a + a ≠ c + c ∧ b + b ≠ c + c) := by
  by_cases hab : a + a = b + b
  · by_cases hbc : b + b = c + c
    · exact Or.inl ⟨hab, hbc⟩
    · exact Or.inr (Or.inl ⟨hab, hbc⟩)
  · by_cases hac : a + a = c + c
    · exact Or.inr (Or.inr (Or.inl ⟨hab, hac⟩))
    · by_cases hbc : b + b = c + c
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hab, hac, hbc⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hab, hac, hbc⟩)))


/-! ## Exceptional cross-matching: constructive ("if") direction -/

/--
For a doublet differing by a two-torsion element, the nine ordered sums
collapse to one diagonal term and four terms of multiplicity two.
No distinctness hypotheses are needed for the explicit coefficient function.
-/
theorem paired_expansion (a b d z : G) (hd : d + d = 0) :
    tripleSquareCoeff a b (b + d) z =
      (if a + a = z then 1 else 0) +
      2 * ((if b + b = z then 1 else 0) +
           (if b + b + d = z then 1 else 0) +
           (if a + b = z then 1 else 0) +
           (if a + b + d = z then 1 else 0)) := by
  have hdouble : (b + d) + (b + d) = b + b := by
    calc
      (b + d) + (b + d) = (b + b) + (d + d) := by abel
      _ = b + b := by simp [hd]
  have hsingle : a + (b + d) = a + b + d := by abel
  have hpaired : b + (b + d) = b + b + d := by abel
  simp only [tripleSquareCoeff, diagCoeff, offCoeff,
    hdouble, hsingle, hpaired]
  omega

/--
The exceptional partner reflects the doublet about the singleton.
This establishes the SUFFICIENT condition for equal labelled squares;
it does NOT assert the necessity or the complete fibre classification.
The condition 3(b-a)=d permits order-six differences, not merely order three.
-/
theorem exceptional_reflection_same_square
    (a b d z : G) (hd : d + d = 0)
    (h3 : ((b - a) + (b - a)) + (b - a) = 0 ∨
          ((b - a) + (b - a)) + (b - a) = d) :
    tripleSquareCoeff a b (b + d) z =
      tripleSquareCoeff a (b + b - a) ((b + b - a) + d) z := by
  let e : G := b + b - a
  have hae : a + e = b + b := by dsimp [e]; abel
  have hee : e + e =
      (a + b) + (((b - a) + (b - a)) + (b - a)) := by
    dsimp [e]
    abel
  change tripleSquareCoeff a b (b + d) z =
    tripleSquareCoeff a e (e + d) z
  rcases h3 with hzero | hdifference
  · have hee0 : e + e = a + b := by
      rw [hee, hzero]
      simp
    rw [paired_expansion a b d z hd, paired_expansion a e d z hd]
    rw [hee0, hae]
    omega
  · have heed : e + e = a + b + d := by
      rw [hee, hdifference]
    have hflip : (e + e) + d = a + b := by
      calc
        (e + e) + d = (a + b + d) + d := by rw [heed]
        _ = (a + b) + (d + d) := by abel
        _ = a + b := by simp [hd]
    rw [paired_expansion a b d z hd, paired_expansion a e d z hd]
    rw [heed, hae]
    have hflip' : (a + b + d) + d = a + b := by
      calc
        (a + b + d) + d = (a + b) + (d + d) := by abel
        _ = a + b := by simp [hd]
    rw [hflip']
    omega


/-! ## Algebraic prerequisites for the necessary direction -/



/--
If the off-diagonal H-pair of a candidate partner is matched across the
original double-pair, its base has the form 2b-a plus two-torsion toggles.
If its doubled base matches the other original H-pair, the exceptional
condition 3(b-a) in {0,d} is NECESSARY.

The assumptions describe an algebraic cross-matching; deriving them from
arbitrary equal convolution squares is a separate pending theorem.
-/
theorem cross_matching_forces_exception
    (a b c d u : G) (hd : d + d = 0) (hu : u + u = 0)
    (hbase : c = (b + b - a) + u ∨ c = ((b + b - a) + u) + d)
    (hsquare : c + c = a + b ∨ c + c = (a + b) + d) :
    ((b - a) + (b - a)) + (b - a) = 0 ∨
    ((b - a) + (b - a)) + (b - a) = d := by
  have hcc : c + c = (b + b - a) + (b + b - a) := by
    rcases hbase with hc | hc
    · rw [hc]
      calc
        ((b + b - a) + u) + ((b + b - a) + u) =
            ((b + b - a) + (b + b - a)) + (u + u) := by abel
        _ = (b + b - a) + (b + b - a) := by simp [hu]
    · rw [hc]
      calc
        (((b + b - a) + u) + d) + (((b + b - a) + u) + d) =
            ((b + b - a) + (b + b - a)) + ((u + u) + (d + d)) := by abel
        _ = (b + b - a) + (b + b - a) := by simp [hu, hd]
  have hkey : ((b - a) + (b - a)) + (b - a) = (c + c) - (a + b) := by
    rw [hcc]
    abel
  rcases hsquare with hsquare | hsquare
  · left
    calc
      ((b - a) + (b - a)) + (b - a) = (c + c) - (a + b) := hkey
      _ = 0 := by rw [hsquare]; simp
  · right
    calc
      ((b - a) + (b - a)) + (b - a) = (c + c) - (a + b) := hkey
      _ = d := by rw [hsquare]; abel


/-! ## From arbitrary equal squares to the singleton and residual identities -/

/-- An explicit indicator encoding the four even-multiplicity sums of a paired triple. -/
def residualCoeff (a b d z : G) : ℕ :=
  (if b + b = z then 1 else 0) +
  (if b + b + d = z then 1 else 0) +
  (if a + b = z then 1 else 0) +
  (if a + b + d = z then 1 else 0)

theorem paired_expansion_residual (a b d z : G) (hd : d + d = 0) :
    tripleSquareCoeff a b (b + d) z =
      (if a + a = z then 1 else 0) + 2 * residualCoeff a b d z := by
  simpa only [residualCoeff] using paired_expansion a b d z hd

/-- The full paired square has exactly the parity of its singleton diagonal. -/
theorem paired_square_parity (a b d z : G) (hd : d + d = 0) :
    tripleSquareCoeff a b (b + d) z % 2 =
      (if a + a = z then 1 else 0) := by
  rw [paired_expansion_residual a b d z hd]
  by_cases h : a + a = z
  · simp only [if_pos h]
    omega
  · simp only [if_neg h]
    omega

/--
Any equality of two labelled paired-triple convolution squares forces equality
of their singleton doubling values. This is NOT an assumption of a cross match.
-/
theorem singleton_doubles_equal_of_square_eq
    (a b t c d e : G) (hd : d + d = 0) (he : e + e = 0)
    (hsq : ∀ z : G,
      tripleSquareCoeff a b (b + d) z =
        tripleSquareCoeff t c (c + e) z) :
    a + a = t + t := by
  have hp := congrArg (fun n : ℕ => n % 2) (hsq (a + a))
  change tripleSquareCoeff a b (b + d) (a + a) % 2 =
    tripleSquareCoeff t c (c + e) (a + a) % 2 at hp
  rw [paired_square_parity a b d (a + a) hd,
      paired_square_parity t c e (a + a) he] at hp
  by_contra hne
  have ht : t + t ≠ a + a := Ne.symm hne
  simp [ht] at hp

/--
Every paired-profile collision can be translated by a 2-torsion element
to have the SAME singleton a. The remaining comparison is then between two
four-term residual coefficients.
-/
theorem normalize_paired_square_singleton
    (a b t c d e : G) (hd : d + d = 0) (he : e + e = 0)
    (hsq : ∀ z : G,
      tripleSquareCoeff a b (b + d) z =
        tripleSquareCoeff t c (c + e) z) :
    ∃ u : G, u + u = 0 ∧ t + u = a ∧
      (∀ z : G,
        tripleSquareCoeff a b (b + d) z =
          tripleSquareCoeff a (c + u) ((c + u) + e) z) := by
  have hdouble : t + t = a + a :=
    (singleton_doubles_equal_of_square_eq a b t c d e hd he hsq).symm
  let u : G := a - t
  have hu : u + u = 0 := by
    change (a - t) + (a - t) = 0
    exact (double_eq_iff_two_torsion t a).mp hdouble
  have htu : t + u = a := by
    dsimp [u]
    abel
  refine ⟨u, hu, htu, ?_⟩
  intro z
  calc
    tripleSquareCoeff a b (b + d) z =
        tripleSquareCoeff t c (c + e) z := hsq z
    _ = tripleSquareCoeff (t + u) (c + u) ((c + e) + u) z :=
      (tripleSquareCoeff_translate t c (c + e) u z hu).symm
    _ = tripleSquareCoeff a (c + u) ((c + u) + e) z := by
      have hc : (c + e) + u = (c + u) + e := by abel
      rw [htu, hc]

/-- After aligning singletons, equality of squares cancels to four-term equality. -/
theorem residual_eq_of_square_eq_same_singleton
    (a b c d e : G) (hd : d + d = 0) (he : e + e = 0)
    (hsq : ∀ z : G,
      tripleSquareCoeff a b (b + d) z =
        tripleSquareCoeff a c (c + e) z) :
    ∀ z : G, residualCoeff a b d z = residualCoeff a c e z := by
  intro z
  have h := hsq z
  rw [paired_expansion_residual a b d z hd,
      paired_expansion_residual a c e z he] at h
  omega




/-! ## Exhaustiveness of the two residual pair-coset matchings -/

/-- Two points of the form x and x+d, with 2d=0, have the same double. -/
theorem double_of_pair_member (x d z : G) (hd : d + d = 0)
    (hz : z = x ∨ z = x + d) : z + z = x + x := by
  rcases hz with hz | hz
  · simpa [hz]
  · rw [hz]
    calc
      (x + d) + (x + d) = (x + x) + (d + d) := by abel
      _ = x + x := by simp [hd]

/-- Any positive residual coefficient comes from one of the four displayed sums. -/
theorem residual_positive_cases (a b d z : G)
    (hp : 0 < residualCoeff a b d z) :
    z = b + b ∨ z = b + b + d ∨ z = a + b ∨ z = a + b + d := by
  by_contra hn
  have h1 : b + b ≠ z := by
    intro h; exact hn (Or.inl h.symm)
  have h2 : b + b + d ≠ z := by
    intro h; exact hn (Or.inr (Or.inl h.symm))
  have h3 : a + b ≠ z := by
    intro h; exact hn (Or.inr (Or.inr (Or.inl h.symm)))
  have h4 : a + b + d ≠ z := by
    intro h; exact hn (Or.inr (Or.inr (Or.inr h.symm)))
  simp [residualCoeff, h1, h2, h3, h4] at hp

/-- The two distinguished bases of a residual pair-profile have positive coefficients. -/
theorem residual_double_base_positive (a c e : G) :
    0 < residualCoeff a c e (c + c) := by
  simp [residualCoeff] <;> omega

theorem residual_mixed_base_positive (a c e : G) :
    0 < residualCoeff a c e (a + c) := by
  simp [residualCoeff] <;> omega

/-- Equal residual functions place each candidate base among four source sums. -/
theorem residual_partner_base_in_four
    (a b c d e z : G)
    (hres : ∀ w : G, residualCoeff a b d w = residualCoeff a c e w)
    (hz : z = c + c ∨ z = a + c) :
    z = b + b ∨ z = b + b + d ∨ z = a + b ∨ z = a + b + d := by
  have hpos : 0 < residualCoeff a c e z := by
    rcases hz with hz | hz
    · simpa [hz] using residual_double_base_positive a c e
    · simpa [hz] using residual_mixed_base_positive a c e
  apply residual_positive_cases a b d z
  rw [hres z]
  exact hpos

/--
If two bases have equal doubles, the singleton and doublet lie in the
same doubling fibre. This is prohibited in a genuine (1,2) profile.
-/
theorem bases_cannot_share_double_pair
    (a c x d : G) (hd : d + d = 0)
    (hac : a + a ≠ c + c)
    (hp : c + c = x ∨ c + c = x + d)
    (hq : a + c = x ∨ a + c = x + d) : False := by
  have hp2 := double_of_pair_member x d (c + c) hd hp
  have hq2 := double_of_pair_member x d (a + c) hd hq
  have h : (c + c) + (c + c) = (a + c) + (a + c) :=
    hp2.trans hq2.symm
  have hz : (a + a) - (c + c) = 0 := by
    calc
      (a + a) - (c + c) =
        ((a + c) + (a + c)) - ((c + c) + (c + c)) := by abel
      _ = 0 := by rw [← h]; simp
  exact hac (sub_eq_zero.mp hz)

/--
This is the EXHAUSTIVE direct/cross matching of the *two base cosets*
of four residual contributions. It follows from equality of residual
coefficients and a genuine (1,2) profile, with no matching assumed.
To classify the individual lifts we still need to show e=d and align
each two-point H-pair.
-/
theorem residual_base_matching_dichotomy
    (a b c d e : G) (hd : d + d = 0)
    (hac : a + a ≠ c + c)
    (hres : ∀ z : G, residualCoeff a b d z = residualCoeff a c e z) :
    (((c + c = b + b ∨ c + c = b + b + d) ∧
      (a + c = a + b ∨ a + c = a + b + d)) ∨
     ((c + c = a + b ∨ c + c = a + b + d) ∧
      (a + c = b + b ∨ a + c = b + b + d))) := by
  have hc := residual_partner_base_in_four a b c d e (c + c) hres (Or.inl rfl)
  have ha := residual_partner_base_in_four a b c d e (a + c) hres (Or.inr rfl)
  have hcg : (c + c = b + b ∨ c + c = b + b + d) ∨
      (c + c = a + b ∨ c + c = a + b + d) := by
    rcases hc with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hag : (a + c = b + b ∨ a + c = b + b + d) ∨
      (a + c = a + b ∨ a + c = a + b + d) := by
    rcases ha with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hcg with hb | hab
  · rcases hag with hbc | hacb
    · exact False.elim (bases_cannot_share_double_pair a c (b + b) d hd hac hb hbc)
    · exact Or.inl ⟨hb, hacb⟩
  · rcases hag with hbc | hacb
    · exact Or.inr ⟨hab, hbc⟩
    · exact False.elim (bases_cannot_share_double_pair a c (a + b) d hd hac hab hacb)


/-! ## Lifting residual base matching to the two-torsion direction -/

/-- Two distinct members of a two-torsion pair determine its direction. -/
theorem direction_of_two_matched_endpoints
    (x y d e : G) (hd : d + d = 0) (he0 : e ≠ 0)
    (hy : y = x ∨ y = x + d)
    (hye : y + e = x ∨ y + e = x + d) : e = d := by
  rcases hy with hy | hy
  · rcases hye with hye | hye
    · exfalso
      apply he0
      have h : x + e = x + 0 := by simpa [hy] using hye
      exact add_left_cancel h
    · have h : x + e = x + d := by simpa [hy] using hye
      exact add_left_cancel h
  · rcases hye with hye | hye
    · have hde : d + e = 0 := by
        have h : x + (d + e) = x + 0 := by
          calc
            x + (d + e) = (x + d) + e := by abel
            _ = x := by simpa [hy] using hye
            _ = x + 0 := by simp
        exact add_left_cancel h
      calc
        e = e + (d + d) := by simp [hd]
        _ = (d + e) + d := by abel
        _ = d := by rw [hde]; simp
    · exfalso
      apply he0
      have h : (x + d) + e = (x + d) + 0 := by simpa [hy] using hye
      exact add_left_cancel h

/-- Distinct doubling fibres yield distinct doubles of the residual bases. -/
theorem residual_base_doubles_distinct
    (a b : G) (hab : a + a ≠ b + b) :
    (b + b) + (b + b) ≠ (a + b) + (a + b) := by
  intro h
  apply hab
  have hz : (a + a) - (b + b) = 0 := by
    calc
      (a + a) - (b + b) =
          ((a + b) + (a + b)) - ((b + b) + (b + b)) := by abel
      _ = 0 := by rw [← h]; simp
  exact sub_eq_zero.mp hz

/--
Equality of the four residual coefficients forces equality of the
nonzero two-torsion directions. This is an additional NECESSARY lemma,
not a proof of the complete three-profile classification.
-/
theorem residual_directions_equal
    (a b c d e : G)
    (hd : d + d = 0) (he : e + e = 0) (he0 : e ≠ 0)
    (hab : a + a ≠ b + b)
    (hres : ∀ z : G, residualCoeff a b d z = residualCoeff a c e z) :
    e = d := by
  have hbase :=
    residual_partner_base_in_four a b c d e (c + c) hres (Or.inl rfl)
  have hpos : 0 < residualCoeff a c e ((c + c) + e) := by
    simp [residualCoeff] <;> omega
  have hend :
      (c + c) + e = b + b ∨ (c + c) + e = b + b + d ∨
      (c + c) + e = a + b ∨ (c + c) + e = a + b + d := by
    apply residual_positive_cases a b d
    rw [hres]
    exact hpos
  have hsame :
      (c + c) + (c + c) = ((c + c) + e) + ((c + c) + e) :=
    (pair_sum_translate (c + c) (c + c) e he).symm
  have hseparate := residual_base_doubles_distinct a b hab
  have hclass :
      (c + c = b + b ∨ c + c = b + b + d) ∨
      (c + c = a + b ∨ c + c = a + b + d) := by
    rcases hbase with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases hclass with hp | hq
  · have hbp := double_of_pair_member (b + b) d (c + c) hd hp
    have hep :
        (c + c) + e = b + b ∨ (c + c) + e = b + b + d := by
      rcases hend with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have hc := double_of_pair_member (a + b) d ((c + c) + e) hd
          (Or.inl h)
        exact False.elim (hseparate (hbp.symm.trans (hsame.trans hc)))
      · have hc := double_of_pair_member (a + b) d ((c + c) + e) hd
          (Or.inr h)
        exact False.elim (hseparate (hbp.symm.trans (hsame.trans hc)))
    exact direction_of_two_matched_endpoints (b + b) (c + c) d e hd he0 hp hep
  · have hbq := double_of_pair_member (a + b) d (c + c) hd hq
    have heq :
        (c + c) + e = a + b ∨ (c + c) + e = a + b + d := by
      rcases hend with h | h | h | h
      · have hc := double_of_pair_member (b + b) d ((c + c) + e) hd
          (Or.inl h)
        exact False.elim (hseparate (hc.symm.trans (hsame.symm.trans hbq)))
      · have hc := double_of_pair_member (b + b) d ((c + c) + e) hd
          (Or.inr h)
        exact False.elim (hseparate (hc.symm.trans (hsame.symm.trans hbq)))
      · exact Or.inl h
      · exact Or.inr h
    exact direction_of_two_matched_endpoints (a + b) (c + c) d e hd he0 hq heq


/-! ## Necessary classification in the normalized genuine (1,2) case -/

/--
For two normalized three-point supports with singleton a outside the
doubling fibre of either doublet, equality of their nine ordered-sum
coefficients forces identical nonzero two-torsion directions and either
identical doublets or the exceptional cross-match with 3(b-a) in {0,d}.

This theorem treats only the genuine (1,2) profile. It does NOT establish
universal triple-support classification or fibre counting.
-/
theorem paired_square_classification_same_singleton
    (a b c d e : G)
    (hd : d + d = 0) (he : e + e = 0) (he0 : e ≠ 0)
    (hab : a + a ≠ b + b) (hac : a + a ≠ c + c)
    (hsq : ∀ z : G,
      tripleSquareCoeff a b (b + d) z =
        tripleSquareCoeff a c (c + e) z) :
    e = d ∧
      ((c = b ∨ c = b + d) ∨
       ((c = (b + b - a) ∨ c = (b + b - a) + d) ∧
        (((b - a) + (b - a)) + (b - a) = 0 ∨
         ((b - a) + (b - a)) + (b - a) = d))) := by
  have hres := residual_eq_of_square_eq_same_singleton a b c d e hd he hsq
  have hed : e = d := residual_directions_equal a b c d e hd he he0 hab hres
  refine ⟨hed, ?_⟩
  rcases residual_base_matching_dichotomy a b c d e hd hac hres with
      hdirect | hcross
  · rcases hdirect with ⟨_, hmix⟩
    left
    rcases hmix with h | h
    · exact Or.inl (add_left_cancel h)
    · right
      have h' : a + c = a + (b + d) := by
        calc
          a + c = a + b + d := h
          _ = a + (b + d) := by abel
      exact add_left_cancel h'
  · right
    rcases hcross with ⟨hsquare, hmix⟩
    have hbase : c = b + b - a ∨ c = (b + b - a) + d := by
      rcases hmix with h | h
      · left
        calc
          c = (a + c) - a := by abel
          _ = (b + b) - a := by rw [h]
      · right
        calc
          c = (a + c) - a := by abel
          _ = (b + b + d) - a := by rw [h]
          _ = (b + b - a) + d := by abel
    refine ⟨hbase, ?_⟩
    have hzero : (0 : G) + (0 : G) = 0 := by simp
    have hbase0 : c = (b + b - a) + (0 : G) ∨
        c = ((b + b - a) + (0 : G)) + d := by
      simpa using hbase
    exact cross_matching_forces_exception a b c d 0 hd hzero hbase0 hsquare

/-! ## Reconstruction from the three off-diagonal sums -/

theorem offCoeff_positive_iff (a b c z : G) :
    0 < offCoeff a b c z ↔ z = a + b ∨ z = a + c ∨ z = b + c := by
  unfold offCoeff
  split_ifs <;> aesop

/-- The three labelled edge sums determine a distinct triple up to G[2]. -/
theorem offCoeff_reconstructs_support
    (a b c t v w : G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htv : t ≠ v) (htw : t ≠ w) (hvw : v ≠ w)
    (hoff : ∀ z : G, offCoeff a b c z = offCoeff t v w z) :
    ∃ u : G, u + u = 0 ∧
      ({t, v, w} : Finset G) = {a + u, b + u, c + u} := by
  have he : ({a + b, a + c, b + c} : Finset G) =
      {t + v, t + w, v + w} := by
    ext z
    have hp : (0 < offCoeff a b c z) ↔ (0 < offCoeff t v w z) := by
      rw [hoff z]
    simpa only [offCoeff_positive_iff, Finset.mem_insert,
      Finset.mem_singleton] using hp
  have habac : a + b ≠ a + c := fun h => hbc (add_left_cancel h)
  have habbc : a + b ≠ b + c := by
    intro h
    have h' : b + a = b + c := by simpa [add_comm] using h
    exact hac (add_left_cancel h')
  have hacbc : a + c ≠ b + c := fun h => hab (add_right_cancel h)
  have htvw : t + v ≠ t + w := fun h => hvw (add_left_cancel h)
  have htvm : t + v ≠ v + w := by
    intro h
    have h' : v + t = v + w := by simpa [add_comm] using h
    exact htw (add_left_cancel h')
  have htwm : t + w ≠ v + w := fun h => htv (add_right_cancel h)
  have hs := congrArg (fun s : Finset G => s.sum id) he
  change ({a + b, a + c, b + c} : Finset G).sum id =
    ({t + v, t + w, v + w} : Finset G).sum id at hs
  rw [sum_three (a + b) (a + c) (b + c) habac habbc hacbc,
      sum_three (t + v) (t + w) (v + w) htvw htvm htwm] at hs
  let u : G := (t + v + w) - (a + b + c)
  have hu : u + u = 0 := by
    dsimp [u]
    calc
      ((t + v + w) - (a + b + c)) +
          ((t + v + w) - (a + b + c)) =
        ((t + v) + (t + w) + (v + w)) -
          ((a + b) + (a + c) + (b + c)) := by abel
      _ = 0 := by rw [hs]; simp
  have h1 : (t + v + w) - (a + b) = c + u := by dsimp [u]; abel
  have h2 : (t + v + w) - (a + c) = b + u := by dsimp [u]; abel
  have h3 : (t + v + w) - (b + c) = a + u := by dsimp [u]; abel
  have h4 : (t + v + w) - (t + v) = w := by abel
  have h5 : (t + v + w) - (t + w) = v := by abel
  have h6 : (t + v + w) - (v + w) = t := by abel
  have hi := congrArg (fun s : Finset G => s.image (fun x => (t + v + w) - x)) he
  change ({a + b, a + c, b + c} : Finset G).image (fun x => (t + v + w) - x) =
    ({t + v, t + w, v + w} : Finset G).image (fun x => (t + v + w) - x) at hi
  simp only [Finset.image_insert, Finset.image_singleton, h1, h2, h3, h4, h5, h6] at hi
  refine ⟨u, hu, ?_⟩
  have hleft : ({c + u, b + u, a + u} : Finset G) = {a + u, b + u, c + u} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hright : ({w, v, t} : Finset G) = {t, v, w} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hleft, hright] at hi
  exact hi.symm

/-! ## Profile (1,1,1): parity recovers all diagonals -/

theorem diagCoeff_le_one_distinct_doubles (a b c z : G)
    (hab : a + a ≠ b + b) (hac : a + a ≠ c + c)
    (hbc : b + b ≠ c + c) : diagCoeff a b c z ≤ 1 := by
  unfold diagCoeff
  split_ifs <;> simp_all

theorem distinct_doubles_square_recovers_diagonals
    (a b c t v w : G)
    (hab : a + a ≠ b + b) (hac : a + a ≠ c + c) (hbc : b + b ≠ c + c)
    (htv : t + t ≠ v + v) (htw : t + t ≠ w + w) (hvw : v + v ≠ w + w)
    (hsq : ∀ z : G, tripleSquareCoeff a b c z = tripleSquareCoeff t v w z) :
    ∀ z : G, diagCoeff a b c z = diagCoeff t v w z := by
  intro z
  have hp := congrArg (fun n : ℕ => n % 2) (hsq z)
  change tripleSquareCoeff a b c z % 2 = tripleSquareCoeff t v w z % 2 at hp
  rw [tripleSquareCoeff_mod_two, tripleSquareCoeff_mod_two] at hp
  have h1 := diagCoeff_le_one_distinct_doubles a b c z hab hac hbc
  have h2 := diagCoeff_le_one_distinct_doubles t v w z htv htw hvw
  omega

theorem distinct_doubles_square_classification
    (a b c t v w : G)
    (hab : a + a ≠ b + b) (hac : a + a ≠ c + c) (hbc : b + b ≠ c + c)
    (htv : t + t ≠ v + v) (htw : t + t ≠ w + w) (hvw : v + v ≠ w + w)
    (hsq : ∀ z : G, tripleSquareCoeff a b c z = tripleSquareCoeff t v w z) :
    ∃ u : G, u + u = 0 ∧
      ({t, v, w} : Finset G) = {a + u, b + u, c + u} := by
  have hd := distinct_doubles_square_recovers_diagonals a b c t v w
    hab hac hbc htv htw hvw hsq
  have hoff : ∀ z : G, offCoeff a b c z = offCoeff t v w z := by
    intro z
    have h := hsq z
    unfold tripleSquareCoeff at h
    rw [hd z] at h
    omega
  have hab' : a ≠ b := fun h => hab (by rw [h])
  have hac' : a ≠ c := fun h => hac (by rw [h])
  have hbc' : b ≠ c := fun h => hbc (by rw [h])
  have htv' : t ≠ v := fun h => htv (by rw [h])
  have htw' : t ≠ w := fun h => htw (by rw [h])
  have hvw' : v ≠ w := fun h => hvw (by rw [h])
  exact offCoeff_reconstructs_support a b c t v w hab' hac' hbc' htv' htw' hvw' hoff

/-! ## Profile (3): the unique odd diagonal has multiplicity three -/

theorem same_doubles_diagCoeff (a b c z : G)
    (hab : a + a = b + b) (hac : a + a = c + c) :
    diagCoeff a b c z = 3 * (if a + a = z then 1 else 0) := by
  simp only [diagCoeff, ← hab, ← hac]
  omega

theorem same_doubles_square_parity (a b c z : G)
    (hab : a + a = b + b) (hac : a + a = c + c) :
    tripleSquareCoeff a b c z % 2 = (if a + a = z then 1 else 0) := by
  rw [tripleSquareCoeff_mod_two, same_doubles_diagCoeff a b c z hab hac]
  split_ifs <;> omega

theorem same_doubles_square_classification
    (a b c t v w : G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htv : t ≠ v) (htw : t ≠ w) (hvw : v ≠ w)
    (hab2 : a + a = b + b) (hac2 : a + a = c + c)
    (htv2 : t + t = v + v) (htw2 : t + t = w + w)
    (hsq : ∀ z : G, tripleSquareCoeff a b c z = tripleSquareCoeff t v w z) :
    ∃ u : G, u + u = 0 ∧
      ({t, v, w} : Finset G) = {a + u, b + u, c + u} := by
  have hp := congrArg (fun n : ℕ => n % 2) (hsq (a + a))
  change tripleSquareCoeff a b c (a + a) % 2 = tripleSquareCoeff t v w (a + a) % 2 at hp
  rw [same_doubles_square_parity a b c (a + a) hab2 hac2,
      same_doubles_square_parity t v w (a + a) htv2 htw2] at hp
  have hat : a + a = t + t := by
    by_contra h
    simp [Ne.symm h] at hp
  have hd : ∀ z : G, diagCoeff a b c z = diagCoeff t v w z := by
    intro z
    rw [same_doubles_diagCoeff a b c z hab2 hac2,
        same_doubles_diagCoeff t v w z htv2 htw2, hat]
  have hoff : ∀ z : G, offCoeff a b c z = offCoeff t v w z := by
    intro z
    have h := hsq z
    unfold tripleSquareCoeff at h
    rw [hd z] at h
    omega
  exact offCoeff_reconstructs_support a b c t v w hab hac hbc htv htw hvw hoff

/-! ## Separation of the three profiles -/

theorem distinct_doubles_not_single_odd
    (a b c x : G)
    (hab : a + a ≠ b + b) (hac : a + a ≠ c + c) (hbc : b + b ≠ c + c)
    (hpar : ∀ z : G, tripleSquareCoeff a b c z % 2 = (if x = z then 1 else 0)) :
    False := by
  have hpa := hpar (a + a)
  have hpb := hpar (b + b)
  rw [tripleSquareCoeff_mod_two] at hpa hpb
  have hda : diagCoeff a b c (a + a) = 1 := by
    simp [diagCoeff, Ne.symm hab, Ne.symm hac]
  have hdb : diagCoeff a b c (b + b) = 1 := by
    simp [diagCoeff, hab, Ne.symm hbc]
  rw [hda] at hpa
  rw [hdb] at hpb
  have hxa : x = a + a := by
    by_contra h; simp [h] at hpa
  have hxb : x = b + b := by
    by_contra h; simp [h] at hpb
  exact hab (hxa.symm.trans hxb)

theorem distinct_doubles_not_paired_square
    (a b c t v d : G)
    (hab : a + a ≠ b + b) (hac : a + a ≠ c + c) (hbc : b + b ≠ c + c)
    (hd : d + d = 0)
    (hsq : ∀ z : G, tripleSquareCoeff a b c z = tripleSquareCoeff t v (v + d) z) :
    False := by
  apply distinct_doubles_not_single_odd a b c (t + t) hab hac hbc
  intro z
  rw [hsq z, paired_square_parity t v d z hd]

theorem distinct_doubles_not_same_doubles_square
    (a b c t v w : G)
    (hab : a + a ≠ b + b) (hac : a + a ≠ c + c) (hbc : b + b ≠ c + c)
    (htv : t + t = v + v) (htw : t + t = w + w)
    (hsq : ∀ z : G, tripleSquareCoeff a b c z = tripleSquareCoeff t v w z) :
    False := by
  apply distinct_doubles_not_single_odd a b c (t + t) hab hac hbc
  intro z
  rw [hsq z, same_doubles_square_parity t v w z htv htw]

theorem square_positive_cases (a b c z : G)
    (hp : 0 < tripleSquareCoeff a b c z) :
    z = a + a ∨ z = b + b ∨ z = c + c ∨
    z = a + b ∨ z = a + c ∨ z = b + c := by
  by_contra hn
  have h1 : a + a ≠ z := fun h => hn (Or.inl h.symm)
  have h2 : b + b ≠ z := fun h => hn (Or.inr (Or.inl h.symm))
  have h3 : c + c ≠ z := fun h => hn (Or.inr (Or.inr (Or.inl h.symm)))
  have h4 : a + b ≠ z := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h.symm))))
  have h5 : a + c ≠ z := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm)))))
  have h6 : b + c ≠ z := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.symm)))))
  simp [tripleSquareCoeff, diagCoeff, offCoeff, h1, h2, h3, h4, h5, h6] at hp

/-- A profile-(3) square is supported in one coset of G[2]. -/
theorem same_doubles_positive_double (a b c z : G)
    (hab : a + a = b + b) (hac : a + a = c + c)
    (hp : 0 < tripleSquareCoeff a b c z) :
    z + z = (a + a) + (a + a) := by
  rcases square_positive_cases a b c z hp with h | h | h | h | h | h
  · rw [h]
  · rw [h, ← hab]
  · rw [h, ← hac]
  · rw [h]
    calc
      (a + b) + (a + b) = (a + a) + (b + b) := by abel
      _ = (a + a) + (a + a) := by rw [← hab]
  · rw [h]
    calc
      (a + c) + (a + c) = (a + a) + (c + c) := by abel
      _ = (a + a) + (a + a) := by rw [← hac]
  · rw [h]
    calc
      (b + c) + (b + c) = (b + b) + (c + c) := by abel
      _ = (a + a) + (a + a) := by rw [← hab, ← hac]

theorem same_doubles_not_genuine_paired_square
    (a b c t v d : G)
    (hab : a + a = b + b) (hac : a + a = c + c)
    (hd : d + d = 0) (htv : t + t ≠ v + v)
    (hsq : ∀ z : G, tripleSquareCoeff a b c z = tripleSquareCoeff t v (v + d) z) :
    False := by
  have hp : 0 < tripleSquareCoeff t v (v + d) (v + v) := by
    rw [paired_expansion_residual t v d (v + v) hd]
    have h := residual_double_base_positive t v d
    omega
  have hq : 0 < tripleSquareCoeff t v (v + d) (t + v) := by
    rw [paired_expansion_residual t v d (t + v) hd]
    have h := residual_mixed_base_positive t v d
    omega
  rw [← hsq] at hp hq
  have hp2 := same_doubles_positive_double a b c (v + v) hab hac hp
  have hq2 := same_doubles_positive_double a b c (t + v) hab hac hq
  exact residual_base_doubles_distinct t v htv (hp2.trans hq2.symm)

/-! ## Raccordement: unnormalized genuine paired triples -/

theorem paired_square_classification_after_normalization
    (a b t c d e : G)
    (hd : d + d = 0) (he : e + e = 0) (he0 : e ≠ 0)
    (hab : a + a ≠ b + b) (htc : t + t ≠ c + c)
    (hsq : ∀ z : G, tripleSquareCoeff a b (b + d) z =
      tripleSquareCoeff t c (c + e) z) :
    ∃ u : G, u + u = 0 ∧ t + u = a ∧ e = d ∧
      ((c + u = b ∨ c + u = b + d) ∨
       ((c + u = b + b - a ∨ c + u = (b + b - a) + d) ∧
        (((b - a) + (b - a)) + (b - a) = 0 ∨
         ((b - a) + (b - a)) + (b - a) = d))) := by
  obtain ⟨u, hu, htu, hs⟩ := normalize_paired_square_singleton a b t c d e hd he hsq
  have hdouble : a + a = t + t := singleton_doubles_equal_of_square_eq a b t c d e hd he hsq
  have hc : (c + u) + (c + u) = c + c := pair_sum_translate c c u hu
  have hac : a + a ≠ (c + u) + (c + u) := by
    rw [hdouble, hc]
    exact htc
  obtain ⟨hed, hcases⟩ := paired_square_classification_same_singleton a b (c + u) d e
    hd he he0 hab hac hs
  exact ⟨u, hu, htu, hed, hcases⟩

/-! ## Actual ordered square of finite supports -/

/-- Counts all ordered pairs of support elements, including the diagonal. -/
def orderedSquare (S : Finset G) (z : G) : ℕ :=
  S.sum (fun x => S.sum (fun y => if x + y = z then 1 else 0))

def translateSupport (S : Finset G) (u : G) : Finset G :=
  S.image (fun x => x + u)

theorem orderedSquare_three (a b c z : G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orderedSquare ({a, b, c} : Finset G) z = tripleSquareCoeff a b c z := by
  simp [orderedSquare, tripleSquareCoeff, diagCoeff, offCoeff,
    hab, hac, hbc, add_comm]
  omega

theorem translateSupport_three (a b c u : G) :
    translateSupport ({a, b, c} : Finset G) u = {a + u, b + u, c + u} := by
  simp [translateSupport]

theorem translateSupport_twice (S : Finset G) (u : G) (hu : u + u = 0) :
    translateSupport (translateSupport S u) u = S := by
  have h : (fun x : G => (x + u) + u) = id := by
    funext x
    simp [add_assoc, hu]
  simp only [translateSupport, Finset.image_image, Function.comp_def, h, Finset.image_id]

theorem translateSupport_eq_of_reverse (S T : Finset G) (u : G)
    (hu : u + u = 0) (h : translateSupport T u = S) :
    T = translateSupport S u := by
  have hh := congrArg (fun X => translateSupport X u) h
  change translateSupport (translateSupport T u) u = translateSupport S u at hh
  rw [translateSupport_twice T u hu] at hh
  exact hh

theorem displayed_three_distinct (a b c : G)
    (hcard : ({a, b, c} : Finset G).card = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  · intro h
    rw [h] at hcard
    by_cases hc : b = c <;> simp [hc] at hcard
  constructor
  · intro h
    rw [h] at hcard
    by_cases hb : b = c <;> simp [hb] at hcard
  · intro h
    rw [h] at hcard
    by_cases ha : a = c <;> simp [ha] at hcard

theorem paired_entries_distinct (a b d : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hab : a + a ≠ b + b) :
    a ≠ b ∧ a ≠ b + d ∧ b ≠ b + d := by
  constructor
  · intro h; exact hab (by rw [h])
  constructor
  · intro h
    apply hab
    rw [h]
    exact pair_sum_translate b b d hd
  · intro h
    have h' : b + 0 = b + d := by simpa using h
    exact hd0 (add_left_cancel h').symm

theorem orderedSquare_paired (a b d z : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hab : a + a ≠ b + b) :
    orderedSquare ({a, b, b + d} : Finset G) z = tripleSquareCoeff a b (b + d) z := by
  obtain ⟨h1, h2, h3⟩ := paired_entries_distinct a b d hd hd0 hab
  exact orderedSquare_three a b (b + d) z h1 h2 h3

def OrdinaryPartner (S T : Finset G) : Prop :=
  ∃ u : G, u + u = 0 ∧ T = translateSupport S u

def ExceptionalPartner (S T : Finset G) : Prop :=
  ∃ a b d u : G, d + d = 0 ∧ d ≠ 0 ∧ a + a ≠ b + b ∧ u + u = 0 ∧
    ((((b - a) + (b - a)) + (b - a) = 0) ∨
      (((b - a) + (b - a)) + (b - a) = d)) ∧
    S = {a, b, b + d} ∧
    T = translateSupport ({a, b + b - a, (b + b - a) + d} : Finset G) u

theorem support_swap_last (a b c : G) :
    ({a, b, c} : Finset G) = {a, c, b} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem support_rotate (a b c : G) :
    ({a, b, c} : Finset G) = {b, c, a} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem paired_shape_from_equal_doubles (a b c : G)
    (hab : a ≠ b) (hab2 : a + a = b + b) (hca2 : c + c ≠ a + a) :
    ∃ d : G, d + d = 0 ∧ d ≠ 0 ∧ c + c ≠ a + a ∧
      ({a, b, c} : Finset G) = {c, a, a + d} := by
  let d := b - a
  have hd : d + d = 0 := (double_eq_iff_two_torsion a b).mp hab2
  have hd0 : d ≠ 0 := by
    intro h
    have hba : b = a := sub_eq_zero.mp h
    exact hab hba.symm
  have had : a + d = b := by dsimp [d]; abel
  refine ⟨d, hd, hd0, hca2, ?_⟩
  rw [had]
  exact (support_rotate c a b).symm

/-- Every cardinality-three finite support has one of the three exact shapes. -/
theorem card_three_doubling_shapes (S : Finset G) (hS : S.card = 3) :
    (∃ a b c : G, S = {a, b, c} ∧
      a + a ≠ b + b ∧ a + a ≠ c + c ∧ b + b ≠ c + c) ∨
    (∃ a b c : G, S = {a, b, c} ∧
      a + a = b + b ∧ a + a = c + c) ∨
    (∃ a b d : G, d + d = 0 ∧ d ≠ 0 ∧ a + a ≠ b + b ∧ S = {a, b, b + d}) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  rcases three_doubling_profiles a b c with h | h | h | h | h
  · exact Or.inr (Or.inl ⟨a, b, c, rfl, h.1, h.1.trans h.2⟩)
  · obtain ⟨d, hd, hd0, hca, hs⟩ :=
      paired_shape_from_equal_doubles a b c hab h.1 (by rw [h.1]; exact Ne.symm h.2)
    exact Or.inr (Or.inr ⟨c, a, d, hd, hd0, hca, hs⟩)
  · obtain ⟨d, hd, hd0, hba, hs⟩ :=
      paired_shape_from_equal_doubles a c b hac h.2 (Ne.symm h.1)
    exact Or.inr (Or.inr ⟨b, a, d, hd, hd0, hba, (support_swap_last a b c).trans hs⟩)
  · obtain ⟨d, hd, hd0, hab2, hs⟩ :=
      paired_shape_from_equal_doubles b c a hbc h.2.2 h.1
    exact Or.inr (Or.inr ⟨a, b, d, hd, hd0, hab2, (support_rotate a b c).trans hs⟩)
  · exact Or.inl ⟨a, b, c, rfl, h⟩

/-- Converts equality of actual squares to equality of the explicit expansions. -/
theorem explicit_square_eq_of_orderedSquare_eq
    (S T : Finset G) (a b c t v w : G)
    (hS : S.card = 3) (hT : T.card = 3)
    (hsa : S = {a, b, c}) (htt : T = {t, v, w})
    (hsq : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    ∀ z : G, tripleSquareCoeff a b c z = tripleSquareCoeff t v w z := by
  have hs3 : ({a, b, c} : Finset G).card = 3 := by rw [← hsa]; exact hS
  have ht3 : ({t, v, w} : Finset G).card = 3 := by rw [← htt]; exact hT
  obtain ⟨h1, h2, h3⟩ := displayed_three_distinct a b c hs3
  obtain ⟨h4, h5, h6⟩ := displayed_three_distinct t v w ht3
  intro z
  have h := hsq z
  rw [hsa, htt, orderedSquare_three a b c z h1 h2 h3,
      orderedSquare_three t v w z h4 h5 h6] at h
  exact h

theorem ordinaryPartner_of_explicit_translation (S T : Finset G)
    (a b c t v w u : G) (hu : u + u = 0)
    (hS : S = {a, b, c}) (hT : T = {t, v, w})
    (heq : ({t, v, w} : Finset G) = {a + u, b + u, c + u}) :
    OrdinaryPartner S T := by
  refine ⟨u, hu, ?_⟩
  rw [hS, hT, translateSupport_three]
  exact heq

/-- Derives the support alternative for arbitrary singleton locations in paired shapes. -/
theorem paired_orderedSquare_partner (S T : Finset G)
    (a b t c d e : G) (hS : S.card = 3) (hT : T.card = 3)
    (hd : d + d = 0) (he : e + e = 0) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hab : a + a ≠ b + b) (htc : t + t ≠ c + c)
    (hsa : S = {a, b, b + d}) (htt : T = {t, c, c + e})
    (hsq : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    OrdinaryPartner S T ∨ ExceptionalPartner S T := by
  have hexp := explicit_square_eq_of_orderedSquare_eq S T a b (b + d) t c (c + e)
    hS hT hsa htt hsq
  obtain ⟨u, hu, htu, hed, hcases⟩ :=
    paired_square_classification_after_normalization a b t c d e hd he he0 hab htc hexp
  have hlast : (c + e) + u = (c + u) + e := by abel
  have hnorm : translateSupport T u = ({a, c + u, (c + u) + d} : Finset G) := by
    rw [htt, translateSupport_three, htu, hlast, hed]
  have hflip : (b + d) + d = b := by simp [add_assoc, hd]
  rcases hcases with hdirect | ⟨hcross, h3⟩
  · left
    have hTS : translateSupport T u = S := by
      rw [hnorm, hsa]
      rcases hdirect with h | h
      · rw [h]
      · rw [h, hflip]
        exact support_swap_last a (b + d) b
    exact ⟨u, hu, translateSupport_eq_of_reverse S T u hu hTS⟩
  · right
    have hTR : translateSupport T u =
        ({a, b + b - a, (b + b - a) + d} : Finset G) := by
      rw [hnorm]
      rcases hcross with h | h
      · rw [h]
      · rw [h]
        have hf : ((b + b - a) + d) + d = b + b - a := by simp [add_assoc, hd]
        rw [hf]
        exact support_swap_last a ((b + b - a) + d) (b + b - a)
    exact ⟨a, b, d, u, hd, hd0, hab, hu, h3, hsa,
      translateSupport_eq_of_reverse _ T u hu hTR⟩

/-- Exhaustive necessary classification of actual squares of three-element supports. -/
theorem orderedSquare_classification_necessary (S T : Finset G)
    (hS : S.card = 3) (hT : T.card = 3)
    (hsq : ∀ z : G, orderedSquare S z = orderedSquare T z) :
    OrdinaryPartner S T ∨ ExceptionalPartner S T := by
  rcases card_three_doubling_shapes S hS with
    ⟨a, b, c, hsa, hab, hac, hbc⟩ | ⟨a, b, c, hsa, hab, hac⟩ |
      ⟨a, b, d, hd, hd0, hab, hsa⟩
  · rcases card_three_doubling_shapes T hT with
      ⟨t, v, w, htt, htv, htw, hvw⟩ | ⟨t, v, w, htt, htv, htw⟩ |
        ⟨t, v, e, he, he0, htv, htt⟩
    · have he := explicit_square_eq_of_orderedSquare_eq S T a b c t v w hS hT hsa htt hsq
      obtain ⟨u, hu, heq⟩ := distinct_doubles_square_classification a b c t v w
        hab hac hbc htv htw hvw he
      exact Or.inl (ordinaryPartner_of_explicit_translation S T a b c t v w u hu hsa htt heq)
    · have he := explicit_square_eq_of_orderedSquare_eq S T a b c t v w hS hT hsa htt hsq
      exact (distinct_doubles_not_same_doubles_square a b c t v w hab hac hbc htv htw he).elim
    · have hexp := explicit_square_eq_of_orderedSquare_eq S T a b c t v (v + e) hS hT hsa htt hsq
      exact (distinct_doubles_not_paired_square a b c t v e hab hac hbc he hexp).elim
  · rcases card_three_doubling_shapes T hT with
      ⟨t, v, w, htt, htv, htw, hvw⟩ | ⟨t, v, w, htt, htv, htw⟩ |
        ⟨t, v, e, he, he0, htv, htt⟩
    · have he := explicit_square_eq_of_orderedSquare_eq S T a b c t v w hS hT hsa htt hsq
      exact (distinct_doubles_not_same_doubles_square t v w a b c htv htw hvw hab hac
        (fun z => (he z).symm)).elim
    · have hs3 : ({a, b, c} : Finset G).card = 3 := by rw [← hsa]; exact hS
      have ht3 : ({t, v, w} : Finset G).card = 3 := by rw [← htt]; exact hT
      obtain ⟨h1, h2, h3⟩ := displayed_three_distinct a b c hs3
      obtain ⟨h4, h5, h6⟩ := displayed_three_distinct t v w ht3
      have he := explicit_square_eq_of_orderedSquare_eq S T a b c t v w hS hT hsa htt hsq
      obtain ⟨u, hu, heq⟩ := same_doubles_square_classification a b c t v w
        h1 h2 h3 h4 h5 h6 hab hac htv htw he
      exact Or.inl (ordinaryPartner_of_explicit_translation S T a b c t v w u hu hsa htt heq)
    · have hexp := explicit_square_eq_of_orderedSquare_eq S T a b c t v (v + e) hS hT hsa htt hsq
      exact (same_doubles_not_genuine_paired_square a b c t v e hab hac he htv hexp).elim
  · rcases card_three_doubling_shapes T hT with
      ⟨t, v, w, htt, htv, htw, hvw⟩ | ⟨t, v, w, htt, htv, htw⟩ |
        ⟨t, v, e, he, he0, htv, htt⟩
    · have hexp := explicit_square_eq_of_orderedSquare_eq S T a b (b + d) t v w hS hT hsa htt hsq
      exact (distinct_doubles_not_paired_square t v w a b d htv htw hvw hd
        (fun z => (hexp z).symm)).elim
    · have hexp := explicit_square_eq_of_orderedSquare_eq S T a b (b + d) t v w hS hT hsa htt hsq
      exact (same_doubles_not_genuine_paired_square t v w a b d htv htw hd hab
        (fun z => (hexp z).symm)).elim
    · exact paired_orderedSquare_partner S T a b t v d e hS hT
        hd he hd0 he0 hab htv hsa htt hsq

theorem orderedSquare_translate_of_card_three (S : Finset G)
    (hS : S.card = 3) (u z : G) (hu : u + u = 0) :
    orderedSquare (translateSupport S u) z = orderedSquare S z := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  have habu : a + u ≠ b + u := fun h => hab (add_right_cancel h)
  have hacu : a + u ≠ c + u := fun h => hac (add_right_cancel h)
  have hbcu : b + u ≠ c + u := fun h => hbc (add_right_cancel h)
  rw [translateSupport_three, orderedSquare_three (a + u) (b + u) (c + u) z habu hacu hbcu,
      orderedSquare_three a b c z hab hac hbc]
  exact tripleSquareCoeff_translate a b c u z hu

theorem orderedSquare_eq_of_ordinaryPartner (S T : Finset G)
    (hS : S.card = 3) (h : OrdinaryPartner S T) :
    ∀ z : G, orderedSquare S z = orderedSquare T z := by
  obtain ⟨u, hu, ht⟩ := h
  intro z
  rw [ht, orderedSquare_translate_of_card_three S hS u z hu]

theorem orderedSquare_eq_of_exceptionalPartner (S T : Finset G)
    (hT : T.card = 3) (h : ExceptionalPartner S T) :
    ∀ z : G, orderedSquare S z = orderedSquare T z := by
  obtain ⟨a, b, d, u, hd, hd0, hab, hu, h3, hs, ht⟩ := h
  let f := b + b - a
  have ht' : T = ({a + u, f + u, (f + d) + u} : Finset G) := by
    rw [ht, translateSupport_three]
  have hcard : ({a + u, f + u, (f + d) + u} : Finset G).card = 3 := by
    rw [← ht']; exact hT
  obtain ⟨h1, h2, h4⟩ := displayed_three_distinct (a + u) (f + u) ((f + d) + u) hcard
  intro z
  rw [hs, ht', orderedSquare_paired a b d z hd hd0 hab,
      orderedSquare_three (a + u) (f + u) ((f + d) + u) z h1 h2 h4]
  calc
    tripleSquareCoeff a b (b + d) z = tripleSquareCoeff a f (f + d) z :=
      exceptional_reflection_same_square a b d z hd h3
    _ = tripleSquareCoeff (a + u) (f + u) ((f + d) + u) z :=
      (tripleSquareCoeff_translate a f (f + d) u z hu).symm

/--
Exact classification for cardinality-three finite supports in any abelian group.
The square counts labelled ordered sums including diagonal contributions.
No doubling profile, enumeration, or singleton alignment is assumed.
This theorem does not assert any cardinality/counting or independent audit result.
-/
theorem orderedSquare_classification_iff (S T : Finset G)
    (hS : S.card = 3) (hT : T.card = 3) :
    (∀ z : G, orderedSquare S z = orderedSquare T z) ↔
      OrdinaryPartner S T ∨ ExceptionalPartner S T := by
  constructor
  · exact orderedSquare_classification_necessary S T hS hT
  · intro h
    rcases h with h | h
    · exact orderedSquare_eq_of_ordinaryPartner S T hS h
    · exact orderedSquare_eq_of_exceptionalPartner S T hT h

theorem translateSupport_add (S : Finset G) (u v : G) :
    translateSupport (translateSupport S u) v = translateSupport S (u + v) := by
  have h : (fun x : G => (x + u) + v) = (fun x => x + (u + v)) := by
    funext x; abel
  simp only [translateSupport, Finset.image_image, Function.comp_def, h]

theorem paired_reflection_not_two_torsion_translate (a b d u : G)
    (hd : d + d = 0) (hu : u + u = 0) (hab : a + a ≠ b + b) :
    translateSupport ({a, b, b + d} : Finset G) u ≠
      {a, b + b - a, (b + b - a) + d} := by
  intro heq
  have hm : b + u ∈ translateSupport ({a, b, b + d} : Finset G) u := by
    rw [translateSupport_three]; simp
  rw [heq] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hbu : (b + u) + (b + u) = b + b := pair_sum_translate b b u hu
  rcases hm with hm | hm | hm
  · have hba : b + b = a + a := by rw [← hbu, hm]
    exact hab hba.symm
  · have hbf : b + b = (b + b - a) + (b + b - a) := by
      calc
        b + b = (b + u) + (b + u) := hbu.symm
        _ = (b + b - a) + (b + b - a) := congrArg (fun x => x + x) hm
    apply hab
    apply sub_eq_zero.mp
    calc
      (a + a) - (b + b) = (b + b) - ((b + b - a) + (b + b - a)) := by abel
      _ = (b + b) - (b + b) := congrArg (fun x => (b + b) - x) hbf.symm
      _ = 0 := by simp
  · have hbf : b + b = (b + b - a) + (b + b - a) := by
      calc
        b + b = (b + u) + (b + u) := hbu.symm
        _ = ((b + b - a) + d) + ((b + b - a) + d) := congrArg (fun x => x + x) hm
        _ = (b + b - a) + (b + b - a) := pair_sum_translate (b + b - a) (b + b - a) d hd
    apply hab
    apply sub_eq_zero.mp
    calc
      (a + a) - (b + b) = (b + b) - ((b + b - a) + (b + b - a)) := by abel
      _ = (b + b) - (b + b) := congrArg (fun x => (b + b) - x) hbf.symm
      _ = 0 := by simp

theorem exceptionalPartner_not_ordinaryPartner (S T : Finset G)
    (he : ExceptionalPartner S T) : ¬ OrdinaryPartner S T := by
  obtain ⟨a, b, d, u, hd, _, hab, hu, _, hs, ht⟩ := he
  rintro ⟨v, hv, ht2⟩
  have huv : (v + u) + (v + u) = 0 := by
    calc
      (v + u) + (v + u) = (v + v) + (u + u) := by abel
      _ = 0 := by simp [hv, hu]
  have hTS : translateSupport T u = translateSupport S (v + u) := by
    rw [ht2, translateSupport_add]
  have hTR : translateSupport T u =
      ({a, b + b - a, (b + b - a) + d} : Finset G) := by
    rw [ht, translateSupport_twice _ u hu]
  have heq : translateSupport ({a, b, b + d} : Finset G) (v + u) =
      {a, b + b - a, (b + b - a) + d} := by
    rw [← hs, ← hTS, hTR]
  exact paired_reflection_not_two_torsion_translate a b d (v + u) hd huv hab heq

/-- An exceptional partner is not a translate by any element of the ambient group. -/
theorem exceptionalPartner_not_any_translation (S T : Finset G)
    (hS : S.card = 3) (hT : T.card = 3) (he : ExceptionalPartner S T) :
    ¬ ∃ v : G, T = translateSupport S v := by
  have hsq := orderedSquare_eq_of_exceptionalPartner S T hT he
  have hnot := exceptionalPartner_not_ordinaryPartner S T he
  obtain ⟨a, b, d, u, hd, hd0, hab, hu, h3, hs, ht⟩ := he
  rintro ⟨v, hv⟩
  have hc : (b + d) + v = (b + v) + d := by abel
  have hvT : T = ({a + v, b + v, (b + v) + d} : Finset G) := by
    rw [hv, hs, translateSupport_three, hc]
  have hexp := explicit_square_eq_of_orderedSquare_eq S T a b (b + d)
    (a + v) (b + v) ((b + v) + d) hS hT hs hvT hsq
  have haa := singleton_doubles_equal_of_square_eq a b (a + v) (b + v) d d hd hd hexp
  have hv2 : v + v = 0 := by
    have h := (double_eq_iff_two_torsion a (a + v)).mp haa
    simpa using h
  exact hnot ⟨v, hv2, hv⟩

end Couret.STROBO2TORS


